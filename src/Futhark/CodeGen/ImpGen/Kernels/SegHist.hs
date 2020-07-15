{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Our compilation strategy for 'SegHist' is based around avoiding
-- bin conflicts.  We do this by splitting the input into chunks, and
-- for each chunk computing a single subhistogram.  Then we combine
-- the subhistograms using an ordinary segmented reduction ('SegRed').
--
-- There are some branches around to efficiently handle the case where
-- we use only a single subhistogram (because it's large), so that we
-- respect the asymptotics, and do not copy the destination array.
--
-- We also use a heuristic strategy for computing subhistograms in
-- local memory when possible.  Given:
--
-- H: total size of histograms in bytes, including any lock arrays.
--
-- G: group size
--
-- T: number of bytes of local memory each thread can be given without
-- impacting occupancy (determined experimentally, e.g. 32).
--
-- LMAX: maximum amount of local memory per workgroup (hard limit).
--
-- We wish to compute:
--
-- COOP: cooperation level (number of threads per subhistogram)
--
-- LH: number of local memory subhistograms
--
-- We do this as:
--
-- COOP = ceil(H / T)
-- LH = ceil((G*T)/H)
-- if COOP <= G && H <= LMAX then
--   use local memory
-- else
--   use global memory

module Futhark.CodeGen.ImpGen.Kernels.SegHist
  ( compileSegHist )
  where

import Control.Monad.Except
import Data.Maybe
import Data.List (foldl', genericLength, zip4, zip6)

import Prelude hiding (quot, rem)

import Futhark.MonadFreshNames
import Futhark.IR.KernelsMem
import qualified Futhark.IR.Mem.IxFun as IxFun
import Futhark.Pass.ExplicitAllocations()
import qualified Futhark.CodeGen.ImpCode.Kernels as Imp
import Futhark.CodeGen.ImpGen
import Futhark.CodeGen.ImpGen.Kernels.SegRed (compileSegRed')
import Futhark.CodeGen.ImpGen.Kernels.Base
import Futhark.Util.IntegralExp (divUp, quot, rem)
import Futhark.Util (chunks, mapAccumLM, maxinum, splitFromEnd, takeLast)
import Futhark.Construct (fullSliceNum)

i32Toi64 :: PrimExp v -> PrimExp v
i32Toi64 = ConvOpExp (SExt Int32 Int64)

data SubhistosInfo = SubhistosInfo { subhistosArray :: VName
                                   , subhistosAlloc :: CallKernelGen ()
                                   }

data SegHistSlug = SegHistSlug
                   { slugOp :: HistOp KernelsMem
                   , slugNumSubhistos :: VName
                   , slugSubhistos :: [SubhistosInfo]
                   , slugAtomicUpdate :: AtomicUpdate KernelsMem KernelEnv
                   }

histoSpaceUsage :: HistOp KernelsMem
                -> Imp.Count Imp.Bytes Imp.Exp
histoSpaceUsage op =
  fmap (ConvOpExp (SExt Int64 Int32)) $ sum $
  map (typeSize .
       (`arrayOfRow` histWidth op) .
       (`arrayOfShape` histShape op)) $
  lambdaReturnType $ histOp op

-- | Figure out how much memory is needed per histogram, both
-- segmented and unsegmented,, and compute some other auxiliary
-- information.
computeHistoUsage :: SegSpace
                  -> HistOp KernelsMem
                  -> CallKernelGen (Imp.Count Imp.Bytes Imp.Exp,
                                    Imp.Count Imp.Bytes Imp.Exp,
                                    SegHistSlug)
computeHistoUsage space op = do
  let segment_dims = init $ unSegSpace space
      num_segments = length segment_dims

  -- Create names for the intermediate array memory blocks,
  -- memory block sizes, arrays, and number of subhistograms.
  num_subhistos <- dPrim "num_subhistos" int32
  subhisto_infos <- forM (zip (histDest op) (histNeutral op)) $ \(dest, ne) -> do
    dest_t <- lookupType dest
    dest_mem <- entryArrayLocation <$> lookupArray dest

    subhistos_mem <-
      sDeclareMem (baseString dest ++ "_subhistos_mem") (Space "device")

    let subhistos_shape = Shape (map snd segment_dims++[Var num_subhistos]) <>
                          stripDims num_segments (arrayShape dest_t)
        subhistos_membind = ArrayIn subhistos_mem $ IxFun.iota $
                            map (primExpFromSubExp int32) $ shapeDims subhistos_shape
        ElemPrim dest_pt = elemType dest_t
    subhistos <- sArray (baseString dest ++ "_subhistos")
                 dest_pt subhistos_shape subhistos_membind

    return $ SubhistosInfo subhistos $ do
      let unitHistoCase =
            emit $
            Imp.SetMem subhistos_mem (memLocationName dest_mem) $
            Space "device"

          multiHistoCase = do
            let num_elems = foldl' (*) (Imp.var num_subhistos int32) $
                            map (toExp' int32) $ arrayDims dest_t
                ElemPrim pt = elemType dest_t

            let subhistos_mem_size =
                  Imp.bytes $
                  Imp.unCount (Imp.elements num_elems `Imp.withElemType` pt)

            sAlloc_ subhistos_mem subhistos_mem_size $ Space "device"
            sReplicate subhistos ne
            subhistos_t <- lookupType subhistos
            let slice = fullSliceNum (map (toExp' int32) $ arrayDims subhistos_t) $
                        map (unitSlice 0 . toExp' int32 . snd) segment_dims ++
                        [DimFix 0]
            sUpdate subhistos slice $ Var dest

      sIf (Imp.var num_subhistos int32 .==. 1) unitHistoCase multiHistoCase

  let h = histoSpaceUsage op
      segmented_h = h * product (map (Imp.bytes . toExp' int32) $ init $ segSpaceDims space)

  atomics <- hostAtomics <$> askEnv

  return (h,
          segmented_h,
          SegHistSlug op num_subhistos subhisto_infos $
          atomicUpdateLocking atomics $ histOp op)

prepareAtomicUpdateGlobal :: Maybe Locking -> [VName] -> SegHistSlug
                          -> CallKernelGen (Maybe Locking,
                                            [Imp.Exp] -> InKernelGen ())
prepareAtomicUpdateGlobal l dests slug =
  -- We need a separate lock array if the operators are not all of a
  -- particularly simple form that permits pure atomic operations.
  case (l, slugAtomicUpdate slug) of
    (_, AtomicPrim f) -> return (l, f (Space "global") dests)
    (_, AtomicCAS f) -> return (l, f (Space "global") dests)
    (Just l', AtomicLocking f) -> return (l, f l' (Space "global") dests)
    (Nothing, AtomicLocking f) -> do
      -- The number of locks used here is too low, but since we are
      -- currently forced to inline a huge list, I'm keeping it down
      -- for now.  Some quick experiments suggested that it has little
      -- impact anyway (maybe the locking case is just too slow).
      --
      -- A fun solution would also be to use a simple hashing
      -- algorithm to ensure good distribution of locks.
      let num_locks = 100151
          dims = map (toExp' int32) $
                 shapeDims (histShape (slugOp slug)) ++
                 [ Var (slugNumSubhistos slug)
                 , histWidth (slugOp slug)]
      locks <-
        sStaticArray "hist_locks" (Space "device") int32 $
        Imp.ArrayZeros num_locks
      let l' = Locking locks 0 1 0 (pure . (`rem` fromIntegral num_locks) . flattenIndex dims)
      return (Just l', f l' (Space "global") dests)

-- | Some kernel bodies are not safe (or efficient) to execute
-- multiple times.
data Passage = MustBeSinglePass | MayBeMultiPass deriving (Eq, Ord)

bodyPassage :: KernelBody KernelsMem -> Passage
bodyPassage kbody
  | mempty == consumedInKernelBody (aliasAnalyseKernelBody kbody) =
      MayBeMultiPass
  | otherwise =
      MustBeSinglePass

prepareIntermediateArraysGlobal :: Passage -> Imp.Exp -> Imp.Exp -> [SegHistSlug]
                                -> CallKernelGen
                                   (Imp.Exp,
                                    [[Imp.Exp] -> InKernelGen ()])
prepareIntermediateArraysGlobal passage hist_T hist_N slugs = do
  -- The paper formulae assume there is only one histogram, but in our
  -- implementation there can be multiple that have been horisontally
  -- fused.  We do a bit of trickery with summings and averages to
  -- pretend there is really only one.  For the case of a single
  -- histogram, the actual calculations should be the same as in the
  -- paper.

  -- The sum of all Hs.
  hist_H <- dPrimVE "hist_H" . sum =<< mapM (toExp . histWidth . slugOp) slugs

  hist_RF <- dPrimVE "hist_RF" $
    sum (map (r64 . toExp' int32 . histRaceFactor . slugOp) slugs)
    / r64 (genericLength slugs)

  hist_el_size <- dPrimVE "hist_el_size" $ sum $ map slugElAvgSize slugs

  hist_C_max <- dPrimVE "hist_C_max" $
    Imp.BinOpExp (FMin Float64) (r64 hist_T) $ r64 hist_H / hist_k_ct_min

  hist_M_min <- dPrimVE "hist_M_min" $
    Imp.BinOpExp (SMax Int32) 1 $ t64 $ r64 hist_T / hist_C_max

  -- Querying L2 cache size is not reliable.  Instead we provide a
  -- tunable knob with a hopefully sane default.
  let hist_L2_def = 4 * 1024 * 1024
  hist_L2 <- dPrim "L2_size" int32
  entry <- askFunction
  -- Equivalent to F_L2*L2 in paper.
  sOp $ Imp.GetSize hist_L2
    (keyWithEntryPoint entry $ nameFromString (pretty hist_L2)) $
    Imp.SizeBespoke (nameFromString "L2_for_histogram") hist_L2_def

  let hist_L2_ln_sz = 16*4 -- L2 cache line size approximation

  hist_RACE_exp <- dPrimVE "hist_RACE_exp" $
    Imp.BinOpExp (FMax Float64) 1 $
    (hist_k_RF * hist_RF) /
    (hist_L2_ln_sz / r64 hist_el_size)

  hist_S <- dPrim "hist_S" int32

  -- For sparse histograms (H exceeds N) we only want a single chunk.
  sIf (hist_N .<. hist_H)
    (hist_S <-- 1) $
    hist_S <--
    case passage of
      MayBeMultiPass ->
        (hist_M_min * hist_H * hist_el_size) `divUp`
        t64 (hist_F_L2 * r64 (Imp.vi32 hist_L2) * hist_RACE_exp)
      MustBeSinglePass ->
        1

  emit $ Imp.DebugPrint "Race expansion factor (RACE^exp)" $ Just hist_RACE_exp
  emit $ Imp.DebugPrint "Number of chunks (S)" $ Just $ Imp.vi32 hist_S

  histograms <- snd <$> mapAccumLM (onOp (Imp.vi32 hist_L2) hist_M_min (Imp.vi32 hist_S) hist_RACE_exp) Nothing slugs

  return (Imp.vi32 hist_S, histograms)
  where
    hist_k_ct_min = 2 -- Chosen experimentally
    hist_k_RF = 0.75 -- Chosen experimentally
    hist_F_L2 = 0.4 -- Chosen experimentally

    r64 = ConvOpExp (SIToFP Int32 Float64)
    t64 = ConvOpExp (FPToSI Float64 Int32)

    -- "Average element size" as computed by a formula that also takes
    -- locking into account.
    slugElAvgSize slug@(SegHistSlug op _ _ do_op) =
      case do_op of
        AtomicLocking{} ->
          slugElSize slug `quot` (1+genericLength (lambdaReturnType (histOp op)))
        _ ->
          slugElSize slug `quot` genericLength (lambdaReturnType (histOp op))

    -- "Average element size" as computed by a formula that also takes
    -- locking into account.
    slugElSize (SegHistSlug op _ _ do_op) =
      case do_op of
        AtomicLocking{} ->
          ConvOpExp (SExt Int64 Int32) $ unCount $
          sum $ map (typeSize . (`arrayOfShape` histShape op)) $
          Prim int32 : lambdaReturnType (histOp op)
        _ ->
          ConvOpExp (SExt Int64 Int32) $ unCount $ sum $
          map (typeSize . (`arrayOfShape` histShape op)) $
          lambdaReturnType (histOp op)

    onOp hist_L2 hist_M_min hist_S hist_RACE_exp l slug = do
      let SegHistSlug op num_subhistos subhisto_info do_op = slug
      hist_H <- toExp $ histWidth op

      hist_H_chk <- dPrimVE "hist_H_chk" $
                    hist_H `divUp` hist_S

      emit $ Imp.DebugPrint "Chunk size (H_chk)" $ Just hist_H_chk

      hist_k_max <- dPrimVE "hist_k_max" $
        Imp.BinOpExp (FMin Float64)
        (hist_F_L2 * (r64 hist_L2 / r64 (slugElSize slug)) * hist_RACE_exp)
        (r64 hist_N)
        / r64 hist_T

      hist_u <- dPrimVE "hist_u" $
                case do_op of
                  AtomicPrim{} -> 2
                  _            -> 1

      hist_C <- dPrimVE "hist_C" $
                Imp.BinOpExp (FMin Float64) (r64 hist_T) $
                r64 (hist_u * hist_H_chk) / hist_k_max

      -- Number of subhistograms per result histogram.
      hist_M <- dPrimVE "hist_M" $
        case slugAtomicUpdate slug of
          AtomicPrim{} -> 1
          _ -> Imp.BinOpExp (SMax Int32) hist_M_min $
               t64 $ r64 hist_T / hist_C

      emit $ Imp.DebugPrint "Elements/thread in L2 cache (k_max)" $ Just hist_k_max
      emit $ Imp.DebugPrint "Multiplication degree (M)" $ Just hist_M
      emit $ Imp.DebugPrint "Cooperation level (C)" $ Just hist_C

      -- num_subhistos is the variable we use to communicate back.
      num_subhistos <-- hist_M

      -- Initialise sub-histograms.
      --
      -- If hist_M is 1, then we just reuse the original
      -- destination.  The idea is to avoid a copy if we are writing a
      -- small number of values into a very large prior histogram.
      dests <- forM (zip (histDest op) subhisto_info) $ \(dest, info) -> do
        dest_mem <- entryArrayLocation <$> lookupArray dest

        sub_mem <- fmap memLocationName $
                   entryArrayLocation <$>
                   lookupArray (subhistosArray info)

        let unitHistoCase =
              emit $
              Imp.SetMem sub_mem (memLocationName dest_mem) $
              Space "device"

            multiHistoCase = subhistosAlloc info

        sIf (hist_M .==. 1) unitHistoCase multiHistoCase

        return $ subhistosArray info

      (l', do_op') <- prepareAtomicUpdateGlobal l dests slug

      return (l', do_op')

histKernelGlobalPass :: [PatElem KernelsMem]
                     -> Count NumGroups Imp.Exp
                     -> Count GroupSize Imp.Exp
                     -> SegSpace
                     -> [SegHistSlug]
                     -> KernelBody KernelsMem
                     -> [[Imp.Exp] -> InKernelGen ()]
                     -> Imp.Exp -> Imp.Exp
                     -> CallKernelGen ()
histKernelGlobalPass map_pes num_groups group_size space slugs kbody histograms hist_S chk_i = do

  let (space_is, space_sizes) = unzip $ unSegSpace space
      space_sizes_64 = map (i32Toi64 . toExp' int32) space_sizes
      total_w_64 = product space_sizes_64

  hist_H_chks <- forM (map (histWidth . slugOp) slugs) $ \w -> do
    w' <- toExp w
    dPrimVE "hist_H_chk" $ w' `divUp` hist_S

  sKernelThread "seghist_global" num_groups group_size (segFlat space) $ do
    constants <- kernelConstants <$> askEnv

    -- Compute subhistogram index for each thread, per histogram.
    subhisto_inds <- forM slugs $ \slug ->
      dPrimVE "subhisto_ind" $
      kernelGlobalThreadId constants `quot`
      (kernelNumThreads constants `divUp` Imp.vi32 (slugNumSubhistos slug))

    -- Loop over flat offsets into the input and output.  The
    -- calculation is done with 64-bit integers to avoid overflow,
    -- but the final unflattened segment indexes are 32 bit.
    let gtid = i32Toi64 $ kernelGlobalThreadId constants
        num_threads = i32Toi64 $ kernelNumThreads constants
    kernelLoop gtid num_threads total_w_64 $ \offset -> do

      -- Construct segment indices.
      let setIndex v e = do dPrim_ v int32
                            v <-- e
      zipWithM_ setIndex space_is $
        map (ConvOpExp (SExt Int64 Int32)) $ unflattenIndex space_sizes_64 offset

      -- We execute the bucket function once and update each histogram serially.
      -- We apply the bucket function if j=offset+ltid is less than
      -- num_elements.  This also involves writing to the mapout
      -- arrays.
      let input_in_bounds = offset .<. total_w_64

      sWhen input_in_bounds $ compileStms mempty (kernelBodyStms kbody) $ do
        let (red_res, map_res) = splitFromEnd (length map_pes) $ kernelBodyResult kbody

        sComment "save map-out results" $
          forM_ (zip map_pes map_res) $ \(pe, res) ->
          copyDWIMFix (patElemName pe)
          (map (Imp.vi32 . fst) $ unSegSpace space)
          (kernelResultSubExp res) []

        let (buckets, vs) = splitAt (length slugs) red_res
            perOp = chunks $ map (length . histDest . slugOp) slugs

        sComment "perform atomic updates" $
          forM_ (zip6 (map slugOp slugs) histograms buckets (perOp vs) subhisto_inds hist_H_chks) $
          \(HistOp dest_w _ _ _ shape lam,
            do_op, bucket, vs', subhisto_ind, hist_H_chk) -> do

            let chk_beg = chk_i * hist_H_chk
                bucket' = toExp' int32 $ kernelResultSubExp bucket
                dest_w' = toExp' int32 dest_w
                bucket_in_bounds = chk_beg .<=. bucket' .&&.
                                   bucket' .<. (chk_beg + hist_H_chk) .&&.
                                   bucket' .<. dest_w'
                vs_params = takeLast (length vs') $ lambdaParams lam

            sWhen bucket_in_bounds $ do
              let bucket_is = map Imp.vi32 (init space_is) ++
                              [subhisto_ind, bucket']
              dLParams $ lambdaParams lam
              sLoopNest shape $ \is -> do
                forM_ (zip vs_params vs') $ \(p, res) ->
                  copyDWIMFix (paramName p) [] (kernelResultSubExp res) is
                do_op (bucket_is ++ is)


histKernelGlobal :: [PatElem KernelsMem]
                 -> Count NumGroups SubExp -> Count GroupSize SubExp
                 -> SegSpace
                 -> [SegHistSlug]
                 -> KernelBody KernelsMem
                 -> CallKernelGen ()
histKernelGlobal map_pes num_groups group_size space slugs kbody = do
  num_groups' <- traverse toExp num_groups
  group_size' <- traverse toExp group_size
  let (_space_is, space_sizes) = unzip $ unSegSpace space
      num_threads = unCount num_groups' * unCount group_size'

  emit $ Imp.DebugPrint "## Using global memory" Nothing

  (hist_S, histograms) <-
    prepareIntermediateArraysGlobal (bodyPassage kbody)
    num_threads (toExp' int32 $ last space_sizes) slugs

  sFor "chk_i" hist_S $ \chk_i ->
    histKernelGlobalPass map_pes num_groups' group_size' space slugs kbody
    histograms hist_S chk_i

type InitLocalHistograms = [([VName],
                              SubExp ->
                              InKernelGen ([VName],
                                            [Imp.Exp] -> InKernelGen ()))]

prepareIntermediateArraysLocal :: VName
                               -> Count NumGroups Imp.Exp
                               -> SegSpace -> [SegHistSlug]
                               -> CallKernelGen InitLocalHistograms
prepareIntermediateArraysLocal num_subhistos_per_group groups_per_segment space slugs = do
  num_segments <- dPrimVE "num_segments" $
                  product $ map (toExp' int32 . snd) $ init $ unSegSpace space
  mapM (onOp num_segments) slugs
  where
    onOp num_segments (SegHistSlug op num_subhistos subhisto_info do_op) = do

      num_subhistos <-- unCount groups_per_segment * num_segments

      emit $ Imp.DebugPrint "Number of subhistograms in global memory" $
        Just $ Imp.vi32 num_subhistos

      mk_op <-
        case do_op of
          AtomicPrim f -> return $ const $ return f
          AtomicCAS f -> return $ const $ return f
          AtomicLocking f -> return $ \hist_H_chk -> do
            let lock_shape =
                  Shape $ Var num_subhistos_per_group :
                  shapeDims (histShape op) ++
                  [hist_H_chk]

            dims <- mapM toExp $ shapeDims lock_shape

            locks <- sAllocArray "locks" int32 lock_shape $ Space "local"

            sComment "All locks start out unlocked" $
              groupCoverSpace dims $ \is ->
              copyDWIMFix locks is (intConst Int32 0) []

            return $ f $ Locking locks 0 1 0 id

      -- Initialise local-memory sub-histograms.  These are
      -- represented as two-dimensional arrays.
      let init_local_subhistos hist_H_chk = do
            local_subhistos <-
              forM (histType op) $ \t -> do
                let sub_local_shape =
                      Shape [Var num_subhistos_per_group] <>
                      (arrayShape t `setOuterDim` hist_H_chk)
                    ElemPrim pt = elemType t
                sAllocArray "subhistogram_local"
                  pt sub_local_shape (Space "local")

            do_op' <- mk_op hist_H_chk

            return (local_subhistos, do_op' (Space "local") local_subhistos)

      -- Initialise global-memory sub-histograms.
      glob_subhistos <- forM subhisto_info $ \info -> do
        subhistosAlloc info
        return $ subhistosArray info

      return (glob_subhistos, init_local_subhistos)

histKernelLocalPass :: VName -> Count NumGroups Imp.Exp
                    -> [PatElem KernelsMem]
                    -> Count NumGroups Imp.Exp -> Count GroupSize Imp.Exp
                    -> SegSpace
                    -> [SegHistSlug]
                    -> KernelBody KernelsMem
                    -> InitLocalHistograms -> Imp.Exp -> Imp.Exp
                    -> CallKernelGen ()
histKernelLocalPass num_subhistos_per_group_var groups_per_segment map_pes num_groups group_size space slugs kbody
                    init_histograms hist_S chk_i = do
  let (space_is, space_sizes) = unzip $ unSegSpace space
      segment_is = init space_is
      segment_dims = init space_sizes
      (i_in_segment, segment_size) = last $ unSegSpace space
      num_subhistos_per_group = Imp.var num_subhistos_per_group_var int32

  segment_size' <- toExp segment_size

  num_segments <- dPrimVE "num_segments" $
                  product $ map (toExp' int32) segment_dims

  hist_H_chks <- forM (map (histWidth . slugOp) slugs) $ \w -> do
    w' <- toExp w
    dPrimV "hist_H_chk" $ w' `divUp` hist_S

  sKernelThread "seghist_local" num_groups group_size (segFlat space) $
    virtualiseGroups SegVirt (unCount groups_per_segment * num_segments) $ \group_id_var -> do

    constants <- kernelConstants <$> askEnv

    let group_id = Imp.vi32 group_id_var

    flat_segment_id <- dPrimVE "flat_segment_id" $ group_id `quot` unCount groups_per_segment
    gid_in_segment <- dPrimVE "gid_in_segment" $ group_id `rem` unCount groups_per_segment
    -- This pgtid is kind of a "virtualised physical" gtid - not the
    -- same thing as the gtid used for the SegHist itself.
    pgtid_in_segment <- dPrimVE "pgtid_in_segment" $
      gid_in_segment * kernelGroupSize constants + kernelLocalThreadId constants
    threads_per_segment <- dPrimVE "threads_per_segment" $
      unCount groups_per_segment * kernelGroupSize constants

    -- Set segment indices.
    zipWithM_ dPrimV_ segment_is $
      unflattenIndex (map (toExp' int32) segment_dims) flat_segment_id

    histograms <- forM (zip init_histograms hist_H_chks) $
                  \((glob_subhistos, init_local_subhistos), hist_H_chk) -> do
      (local_subhistos, do_op) <- init_local_subhistos $ Var hist_H_chk
      return (zip glob_subhistos local_subhistos, hist_H_chk, do_op)

    -- Find index of local subhistograms updated by this thread.  We
    -- try to ensure, as much as possible, that threads in the same
    -- warp use different subhistograms, to avoid conflicts.
    thread_local_subhisto_i <-
      dPrimVE "thread_local_subhisto_i" $
      kernelLocalThreadId constants `rem` num_subhistos_per_group

    let onSlugs f = forM_ (zip slugs histograms) $ \(slug, (dests, hist_H_chk, _)) -> do
          let histo_dims = fmap (toExp' int32) $ Var hist_H_chk :
                           shapeDims (histShape (slugOp slug))
          histo_size <- dPrimVE "histo_size" $ product histo_dims
          f slug dests (Imp.vi32 hist_H_chk) histo_dims histo_size

    let onAllHistograms f =
          onSlugs $ \slug dests hist_H_chk histo_dims histo_size -> do
            let group_hists_size = num_subhistos_per_group * histo_size
            init_per_thread <- dPrimVE "init_per_thread" $
                               group_hists_size `divUp`
                               kernelGroupSize constants

            forM_ (zip dests (histNeutral $ slugOp slug)) $
              \((dest_global, dest_local), ne) ->
                sFor "local_i" init_per_thread $ \i -> do
                  j <- dPrimVE "j" $
                       i * kernelGroupSize constants +
                       kernelLocalThreadId constants
                  j_offset <- dPrimVE "j_offset" $
                              num_subhistos_per_group * histo_size * gid_in_segment + j

                  local_subhisto_i <- dPrimVE "local_subhisto_i" $ j `quot` histo_size
                  let local_bucket_is = unflattenIndex histo_dims $ j `rem` histo_size
                      global_bucket_is = head local_bucket_is + chk_i * hist_H_chk :
                                         tail local_bucket_is
                  global_subhisto_i <- dPrimVE "global_subhisto_i" $ j_offset `quot` histo_size

                  sWhen (j .<. group_hists_size) $
                    f dest_local dest_global (slugOp slug) ne
                    local_subhisto_i global_subhisto_i
                    local_bucket_is global_bucket_is

    sComment "initialize histograms in local memory" $
      onAllHistograms $ \dest_local dest_global op ne local_subhisto_i global_subhisto_i local_bucket_is global_bucket_is ->
      sComment "First subhistogram is initialised from global memory; others with neutral element." $ do
      let global_is = map Imp.vi32 segment_is ++ [0] ++ global_bucket_is
          local_is = local_subhisto_i : local_bucket_is
      sIf (global_subhisto_i .==. 0)
        (copyDWIMFix dest_local local_is (Var dest_global) global_is)
        (sLoopNest (histShape op) $ \is ->
            copyDWIMFix dest_local (local_is++is) ne [])

    sOp $ Imp.Barrier Imp.FenceLocal

    kernelLoop pgtid_in_segment threads_per_segment segment_size' $ \ie -> do
      dPrimV_ i_in_segment ie

      -- We execute the bucket function once and update each histogram
      -- serially.  This also involves writing to the mapout arrays if
      -- this is the first chunk.

      compileStms mempty (kernelBodyStms kbody) $ do

        let (red_res, map_res) = splitFromEnd (length map_pes) $
                             map kernelResultSubExp $ kernelBodyResult kbody
            (buckets, vs) = splitAt (length slugs) red_res
            perOp = chunks $ map (length . histDest . slugOp) slugs

        sWhen (chk_i .==. 0) $
          sComment "save map-out results" $
          forM_ (zip map_pes map_res) $ \(pe, se) ->
          copyDWIMFix (patElemName pe)
          (map Imp.vi32 space_is) se []

        forM_ (zip4 (map slugOp slugs) histograms buckets (perOp vs)) $
          \(HistOp dest_w _ _ _ shape lam,
            (_, hist_H_chk, do_op), bucket, vs') -> do

            let chk_beg = chk_i * Imp.vi32 hist_H_chk
                bucket' = toExp' int32 bucket
                dest_w' = toExp' int32 dest_w
                bucket_in_bounds = bucket' .<. dest_w' .&&.
                                   chk_beg .<=. bucket' .&&.
                                   bucket' .<. (chk_beg + Imp.vi32 hist_H_chk)
                bucket_is = [thread_local_subhisto_i, bucket' - chk_beg]
                vs_params = takeLast (length vs') $ lambdaParams lam

            sComment "perform atomic updates" $
              sWhen bucket_in_bounds $ do
              dLParams $ lambdaParams lam
              sLoopNest shape $ \is -> do
                forM_ (zip vs_params vs') $ \(p, v) ->
                  copyDWIMFix (paramName p) [] v is
                do_op (bucket_is ++ is)

    sOp $ Imp.ErrorSync Imp.FenceGlobal

    sComment "Compact the multiple local memory subhistograms to result in global memory" $
      onSlugs $ \slug dests hist_H_chk histo_dims histo_size -> do
      bins_per_thread <- dPrimVE "init_per_thread" $
                         histo_size `divUp` kernelGroupSize constants

      trunc_H <- dPrimV "trunc_H" $
                 Imp.BinOpExp (SMin Int32) hist_H_chk $
                 toExp' int32 (histWidth (slugOp slug)) -
                 chk_i * head histo_dims
      let trunc_histo_dims = map (toExp' int32) $ Var trunc_H :
                             shapeDims (histShape (slugOp slug))
      trunc_histo_size <- dPrimVE "histo_size" $ product trunc_histo_dims

      sFor "local_i" bins_per_thread $ \i -> do
        j <- dPrimVE "j" $
             i * kernelGroupSize constants + kernelLocalThreadId constants
        sWhen (j .<. trunc_histo_size) $ do
          -- We are responsible for compacting the flat bin 'j', which
          -- we immediately unflatten.
          let local_bucket_is = unflattenIndex histo_dims j
              global_bucket_is = head local_bucket_is + chk_i * hist_H_chk :
                                 tail local_bucket_is
          dLParams $ lambdaParams $ histOp $ slugOp slug
          let (global_dests, local_dests) = unzip dests
              (xparams, yparams) = splitAt (length local_dests) $
                                   lambdaParams $ histOp $ slugOp slug

          sComment "Read values from subhistogram 0." $
            forM_ (zip xparams local_dests) $ \(xp, subhisto) ->
            copyDWIMFix
            (paramName xp) []
            (Var subhisto) (0:local_bucket_is)

          sComment "Accumulate based on values in other subhistograms." $
            sFor "subhisto_id" (num_subhistos_per_group - 1) $ \subhisto_id -> do
              forM_ (zip yparams local_dests) $ \(yp, subhisto) ->
                copyDWIMFix
                (paramName yp) []
                (Var subhisto) (subhisto_id + 1 : local_bucket_is)
              compileBody' xparams $ lambdaBody $ histOp $ slugOp slug

          sComment "Put final bucket value in global memory." $ do
            let global_is =
                  map Imp.vi32 segment_is ++
                  [group_id `rem` unCount groups_per_segment] ++
                  global_bucket_is
            forM_ (zip xparams global_dests) $ \(xp, global_dest) ->
              copyDWIMFix global_dest global_is (Var $ paramName xp) []

histKernelLocal :: VName -> Count NumGroups Imp.Exp
                -> [PatElem KernelsMem]
                -> Count NumGroups SubExp -> Count GroupSize SubExp
                -> SegSpace
                -> Imp.Exp
                -> [SegHistSlug]
                -> KernelBody KernelsMem
                -> CallKernelGen ()
histKernelLocal num_subhistos_per_group_var groups_per_segment map_pes num_groups group_size space hist_S slugs kbody = do
  num_groups' <- traverse toExp num_groups
  group_size' <- traverse toExp group_size
  let num_subhistos_per_group = Imp.var num_subhistos_per_group_var int32

  emit $ Imp.DebugPrint "Number of local subhistograms per group" $ Just num_subhistos_per_group

  init_histograms <-
    prepareIntermediateArraysLocal num_subhistos_per_group_var groups_per_segment space slugs

  sFor "chk_i" hist_S $ \chk_i ->
    histKernelLocalPass
    num_subhistos_per_group_var groups_per_segment map_pes num_groups' group_size' space slugs kbody
    init_histograms hist_S chk_i

-- | The maximum number of passes we are willing to accept for this
-- kind of atomic update.
slugMaxLocalMemPasses :: SegHistSlug -> Int
slugMaxLocalMemPasses slug =
  case slugAtomicUpdate slug of
    AtomicPrim _ -> 3
    AtomicCAS _  -> 4
    AtomicLocking _ -> 6

localMemoryCase :: [PatElem KernelsMem]
                -> Imp.Exp
                -> SegSpace
                -> Imp.Exp -> Imp.Exp -> Imp.Exp -> Imp.Exp
                -> [SegHistSlug]
                -> KernelBody KernelsMem
                -> CallKernelGen (Imp.Exp, CallKernelGen ())
localMemoryCase map_pes hist_T space hist_H hist_el_size hist_N _ slugs kbody = do
  let space_sizes = segSpaceDims space
      segment_dims = init space_sizes
      segmented = not $ null segment_dims

  hist_L <- dPrim "hist_L" int32
  sOp $ Imp.GetSizeMax hist_L Imp.SizeLocalMemory

  max_group_size <- dPrim "max_group_size" int32
  sOp $ Imp.GetSizeMax max_group_size Imp.SizeGroup
  let group_size = Imp.Count $ Var max_group_size
  num_groups <- fmap (Imp.Count . Var) $ dPrimV "num_groups" $
                hist_T `divUp` toExp' int32 (unCount group_size)
  let num_groups' = toExp' int32 <$> num_groups
      group_size' = toExp' int32 <$> group_size

  let r64 = ConvOpExp (SIToFP Int32 Float64)
      t64 = ConvOpExp (FPToSI Float64 Int32)
      i32_to_i64 = ConvOpExp (SExt Int32 Int64)
      i64_to_i32 = ConvOpExp (SExt Int64 Int32)

  -- M approximation.
  hist_m' <- dPrimVE "hist_m_prime" $
             r64 (Imp.BinOpExp (SMin Int32)
                  (Imp.vi32 hist_L `quot` hist_el_size)
                  (hist_N `divUp` unCount num_groups'))
             / r64 hist_H

  let hist_B = unCount group_size'

  -- M in the paper, but not adjusted for asymptotic efficiency.
  hist_M0 <- dPrimVE "hist_M0" $
             Imp.BinOpExp (SMax Int32) 1 $
             Imp.BinOpExp (SMin Int32) (t64 hist_m') hist_B

  -- Minimal sequential chunking factor.
  let q_small = 2

  -- The number of segments/histograms produced..
  hist_Nout <- dPrimVE "hist_Nout" $ product $ map (toExp' int32) segment_dims

  hist_Nin <- dPrimVE "hist_Nin" $ toExp' int32 $ last space_sizes

  -- Maximum M for work efficiency.
  work_asymp_M_max <-
    if segmented then do

      hist_T_hist_min <- dPrimVE "hist_T_hist_min" $
                         i64_to_i32 $
                         Imp.BinOpExp (SMin Int64)
                         (i32_to_i64 hist_Nin * i32_to_i64 hist_Nout) (i32_to_i64 hist_T)
                         `divUp`
                         i32_to_i64 hist_Nout

      -- Number of groups, rounded up.
      let r = hist_T_hist_min `divUp` hist_B

      dPrimVE "work_asymp_M_max" $ hist_Nin `quot` (r * hist_H)

    else dPrimVE "work_asymp_M_max" $
         (hist_Nout * hist_N) `quot`
         ((q_small * unCount num_groups' * hist_H)
          `quot` genericLength slugs)

  -- Number of subhistograms per result histogram.
  hist_M <- dPrimV "hist_M" $
            Imp.BinOpExp (SMin Int32) hist_M0 work_asymp_M_max

  -- hist_M may be zero (which we'll check for below), but we need it
  -- for some divisions first, so crudely make a nonzero form.
  let hist_M_nonzero = Imp.BinOpExp (SMax Int32) 1 $ Imp.vi32 hist_M

  -- "Cooperation factor" - the number of threads cooperatively
  -- working on the same (sub)histogram.
  hist_C <- dPrimVE "hist_C" $
            hist_B `divUp` hist_M_nonzero

  emit $ Imp.DebugPrint "local hist_M0" $ Just hist_M0
  emit $ Imp.DebugPrint "local work asymp M max" $ Just work_asymp_M_max
  emit $ Imp.DebugPrint "local C" $ Just hist_C
  emit $ Imp.DebugPrint "local B" $ Just hist_B
  emit $ Imp.DebugPrint "local M" $ Just $ Imp.vi32 hist_M
  emit $ Imp.DebugPrint "local memory needed" $
    Just $ hist_H * hist_el_size * Imp.vi32 hist_M

  -- local_mem_needed is what we need to keep a single bucket in local
  -- memory - this is an absolute minimum.  We can fit anything else
  -- by doing multiple passes, although more than a few is
  -- (heuristically) not efficient.
  local_mem_needed <- dPrimVE "local_mem_needed" $ hist_el_size * Imp.vi32 hist_M
  hist_S <- dPrimVE "hist_S" $ (hist_H * local_mem_needed) `divUp` Imp.vi32 hist_L
  let max_S = case bodyPassage kbody of
                MustBeSinglePass -> 1
                MayBeMultiPass -> fromIntegral $ maxinum $ map slugMaxLocalMemPasses slugs

  -- We only use local memory if the number of updates per histogram
  -- at least matches the histogram size, as otherwise it is not
  -- asymptotically efficient.  This mostly matters for the segmented
  -- case.
  let pick_local =
        hist_Nin .>=. hist_H
        .&&. (local_mem_needed .<=. Imp.vi32 hist_L)
        .&&. (hist_S .<=. max_S)
        .&&. hist_C .<=. hist_B
        .&&. Imp.vi32 hist_M .>. 0

      groups_per_segment
        | segmented = num_groups' `divUp` Imp.Count hist_Nout
        | otherwise = num_groups'

      run = do
        emit $ Imp.DebugPrint "## Using local memory" Nothing
        emit $ Imp.DebugPrint "Histogram size (H)" $ Just hist_H
        emit $ Imp.DebugPrint "Multiplication degree (M)" $ Just $ Imp.vi32 hist_M
        emit $ Imp.DebugPrint "Cooperation level (C)" $ Just hist_C
        emit $ Imp.DebugPrint "Number of chunks (S)" $ Just hist_S
        when segmented $
          emit $ Imp.DebugPrint "Groups per segment" $ Just $ unCount groups_per_segment
        histKernelLocal hist_M groups_per_segment map_pes
          num_groups group_size space hist_S slugs kbody

  return (pick_local, run)

-- | Generate code for a segmented histogram called from the host.
compileSegHist :: Pattern KernelsMem
               -> Count NumGroups SubExp -> Count GroupSize SubExp
               -> SegSpace
               -> [HistOp KernelsMem]
               -> KernelBody KernelsMem
               -> CallKernelGen ()
compileSegHist (Pattern _ pes) num_groups group_size space ops kbody = do
  -- Most of this function is not the histogram part itself, but
  -- rather figuring out whether to use a local or global memory
  -- strategy, as well as collapsing the subhistograms produced (which
  -- are always in global memory, but their number may vary).
  num_groups' <- traverse toExp num_groups
  group_size' <- traverse toExp group_size

  dims <- mapM toExp $ segSpaceDims space

  let num_red_res = length ops + sum (map (length . histNeutral) ops)
      (all_red_pes, map_pes) = splitAt num_red_res pes
      segment_size = last dims

  (op_hs, op_seg_hs, slugs) <- unzip3 <$> mapM (computeHistoUsage space) ops
  h <- dPrimVE "h" $ Imp.unCount $ sum op_hs
  seg_h <- dPrimVE "seg_h" $ Imp.unCount $ sum op_seg_hs

  -- Check for emptyness to avoid division-by-zero.
  sUnless (seg_h .==. 0) $ do

    -- Maximum group size (or actual, in this case).
    let hist_B = unCount group_size'

    -- Size of a histogram.
    hist_H <- dPrimVE "hist_H" $ sum $ map (toExp' int32 . histWidth) ops

    -- Size of a single histogram element.  Actually the weighted
    -- average of histogram elements in cases where we have more than
    -- one histogram operation, plus any locks.
    let lockSize slug = case slugAtomicUpdate slug of
                          AtomicLocking{} -> Just $ primByteSize int32
                          _               -> Nothing
    hist_el_size <- dPrimVE "hist_el_size" $ foldl' (+) (h `divUp` hist_H) $
                    mapMaybe lockSize slugs

    -- Input elements contributing to each histogram.
    hist_N <- dPrimVE "hist_N" segment_size

    -- Compute RF as the average RF over all the histograms.
    hist_RF <- dPrimVE "hist_RF" $
               sum (map (toExp' int32. histRaceFactor . slugOp) slugs)
               `quot`
               genericLength slugs

    let hist_T = unCount num_groups' * unCount group_size'
    emit $ Imp.DebugPrint "\n# SegHist" Nothing
    emit $ Imp.DebugPrint "Number of threads (T)" $ Just hist_T
    emit $ Imp.DebugPrint "Desired group size (B)" $ Just hist_B
    emit $ Imp.DebugPrint "Histogram size (H)" $ Just hist_H
    emit $ Imp.DebugPrint "Input elements per histogram (N)" $ Just hist_N
    emit $ Imp.DebugPrint "Number of segments" $
      Just $ product $ map (toExp' int32 . snd) segment_dims
    emit $ Imp.DebugPrint "Histogram element size (el_size)" $ Just hist_el_size
    emit $ Imp.DebugPrint "Race factor (RF)" $ Just hist_RF
    emit $ Imp.DebugPrint "Memory per set of subhistograms per segment" $ Just h
    emit $ Imp.DebugPrint "Memory per set of subhistograms times segments" $ Just seg_h

    (use_local_memory, run_in_local_memory) <-
      localMemoryCase map_pes hist_T space hist_H hist_el_size hist_N hist_RF slugs kbody

    sIf use_local_memory run_in_local_memory $
      histKernelGlobal map_pes num_groups group_size space slugs kbody

    let pes_per_op = chunks (map (length . histDest) ops) all_red_pes

    forM_ (zip3 slugs pes_per_op ops) $ \(slug, red_pes, op) -> do
      let num_histos = slugNumSubhistos slug
          subhistos = map subhistosArray $ slugSubhistos slug

      let unitHistoCase =
            -- This is OK because the memory blocks are at least as
            -- large as the ones we are supposed to use for the result.
            forM_ (zip red_pes subhistos) $ \(pe, subhisto) -> do
              pe_mem <- memLocationName . entryArrayLocation <$>
                        lookupArray (patElemName pe)
              subhisto_mem <- memLocationName . entryArrayLocation <$>
                              lookupArray subhisto
              emit $ Imp.SetMem pe_mem subhisto_mem $ Space "device"

      sIf (Imp.var num_histos int32 .==. 1) unitHistoCase $ do
        -- For the segmented reduction, we keep the segment dimensions
        -- unchanged.  To this, we add two dimensions: one over the number
        -- of buckets, and one over the number of subhistograms.  This
        -- inner dimension is the one that is collapsed in the reduction.
        let num_buckets = histWidth op

        bucket_id <- newVName "bucket_id"
        subhistogram_id <- newVName "subhistogram_id"
        vector_ids <- mapM (const $ newVName "vector_id") $
                      shapeDims $ histShape op

        flat_gtid <- newVName "flat_gtid"

        let lvl = SegThread num_groups group_size SegVirt
            segred_space =
              SegSpace flat_gtid $
              segment_dims ++
              [(bucket_id, num_buckets)] ++
              zip vector_ids (shapeDims $ histShape op) ++
              [(subhistogram_id, Var num_histos)]

        let segred_op = SegBinOp Commutative (histOp op) (histNeutral op) mempty
        compileSegRed' (Pattern [] red_pes) lvl segred_space [segred_op] $ \red_cont ->
          red_cont $ flip map subhistos $ \subhisto ->
            (Var subhisto, map Imp.vi32 $
              map fst segment_dims ++ [subhistogram_id, bucket_id] ++ vector_ids)

  where segment_dims = init $ unSegSpace space
