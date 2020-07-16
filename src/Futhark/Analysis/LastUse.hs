{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Futhark.Analysis.LastUse (lastUseAction, analyseFun, analyseStms, LastUseMap) where

import Control.Monad.IO.Class
import qualified Data.Map as Map
import Data.Map (Map)
import Debug.Trace
import Futhark.Analysis.Alias (aliasAnalysis)
import Futhark.IR.Aliases
import Futhark.IR.KernelsMem
import Futhark.Pipeline

lastUseAction :: Action KernelsMem
lastUseAction =
  Action
    { actionName = "memory allocation lastUse analysis",
      actionDescription = "Perform lastUse analysis on memory allocations",
      actionProcedure = mapM_ analyseAndPrint . progFuns . aliasAnalysis
    }
  where
    analyseAndPrint :: FunDef (Aliases KernelsMem) -> FutharkM ()
    analyseAndPrint fun = do
      liftIO $ putStrLn $ "Analyzing " ++ show (funDefName fun)
      liftIO $ putStrLn $ unwords ["Params:", show $ funDefParams fun]

      let (lumap :: LastUseMap, _) = analyseFun mempty mempty fun

      liftIO $ putStrLn $ unlines $ pretty <$> Map.toList lumap

      liftIO $ putStrLn $ pretty $ funDefBody fun

-- | LastUseMap tells which names were last used in a given statement.
-- Statements are uniquely identified by the 'VName' of the first value
-- parameter in the statement pattern. 'Names' is the set of names last used.
type LastUseMap = Map VName Names

type UsedNames = Names

analyseFun :: LastUseMap -> UsedNames -> FunDef (Aliases KernelsMem) -> (LastUseMap, UsedNames)
analyseFun lu_map used_names fun =
  let (lu_map', used_names') = analyseBody lu_map used_names $ funDefBody fun
   in (lu_map', used_names' <> freeIn (funDefParams fun))

analyseBody :: LastUseMap -> UsedNames -> Body (Aliases KernelsMem) -> (LastUseMap, UsedNames)
analyseBody lu_map used_names (Body ((body_aliases, consumed), ()) stms result) =
  let used_names' =
        used_names
          <> foldMap unAliases body_aliases
          <> unAliases consumed
          <> freeIn result
      (lu_map', used_names'') = analyseStms lu_map used_names stms
   in (lu_map <> lu_map', used_names' <> used_names'')

analyseStms :: LastUseMap -> UsedNames -> Stms (Aliases KernelsMem) -> (LastUseMap, UsedNames)
analyseStms lu_map used_names stms = foldr analyseStm (lu_map, used_names) $ stmsToList stms

analyseStm :: Stm (Aliases KernelsMem) -> (LastUseMap, UsedNames) -> (LastUseMap, UsedNames)
analyseStm (Let pat aux e) (lu_map, used_names) =
  let pat_name = patElemName $ head $ patternValueElements pat
      (lus, lu_map', used_names') = analyseExp (lu_map, used_names) e
      aliases = unAliases $ fst $ stmAuxDec aux
      lus' = (lus `namesSubtract` aliases) `namesSubtract` used_names
   in trace
        (unwords ["analyseStm", pretty pat_name, "aliases", pretty aliases, "lus'", pretty lus'])
        (Map.insert pat_name lus' lu_map', used_names' <> aliases)

analyseExp :: (LastUseMap, UsedNames) -> Exp (Aliases KernelsMem) -> (Names, LastUseMap, UsedNames)
analyseExp (lu_map, used_names) e@(BasicOp _) =
  let nms = freeIn e `namesSubtract` used_names
   in (nms, lu_map, used_names <> nms)
analyseExp (lu_map, used_names) (Apply _ args _ _) =
  let nms = freeIn $ map fst args
   in (nms, lu_map, used_names <> nms)
analyseExp (lu_map, used_names) (If cse then_body else_body dec) =
  let (lu_map_then, used_names_then) = analyseBody lu_map used_names then_body
      (lu_map_else, used_names_else) = analyseBody lu_map used_names else_body
      used_names' = used_names_then <> used_names_else
      nms = (freeIn cse <> freeIn dec) `namesSubtract` used_names'
   in (nms, lu_map_then <> lu_map_else, used_names')
analyseExp (lu_map, used_names) (DoLoop ctx vals form body) =
  let (lu_map', used_names') = analyseBody lu_map used_names body
      nms = (freeIn ctx <> freeIn vals <> freeIn form) `namesSubtract` used_names'
   in (nms, lu_map', used_names' <> nms)
analyseExp (lu_map, used_names) (Op (Alloc se sp)) =
  let nms = (freeIn se <> freeIn sp) `namesSubtract` used_names
   in (nms, lu_map, used_names <> nms)
analyseExp (lu_map, used_names) (Op (Inner (SizeOp sop))) =
  let nms = freeIn sop `namesSubtract` used_names
   in (nms, lu_map, used_names <> nms)
analyseExp (lu_map, used_names) (Op (Inner (OtherOp ()))) =
  (mempty, lu_map, used_names)
analyseExp (lu_map, used_names) (Op (Inner (SegOp (SegMap lvl _ tps body)))) =
  let (lu_map', used_names') = analyseKernelBody (lu_map, used_names) body
      nms = (freeIn lvl <> freeIn tps) `namesSubtract` used_names'
   in (nms, lu_map', used_names' <> nms)
analyseExp (lu_map, used_names) (Op (Inner (SegOp (SegRed lvl _ binops tps body)))) =
  segOpHelper lu_map used_names lvl binops tps body
analyseExp (lu_map, used_names) (Op (Inner (SegOp (SegScan lvl _ binops tps body)))) =
  segOpHelper lu_map used_names lvl binops tps body
analyseExp (lu_map, used_names) (Op (Inner (SegOp (SegHist lvl _ binops tps body)))) =
  let (lu_map', used_names') = foldr analyseHistOp (lu_map, used_names) binops
      (lu_map'', used_names'') = analyseKernelBody (lu_map', used_names') body
      nms = (freeIn lvl <> freeIn tps) `namesSubtract` used_names''
   in (nms, lu_map'', used_names'' <> nms)

segOpHelper :: (Foldable t, FreeIn lvl, FreeIn tps) => Map VName Names -> Names -> lvl -> t (SegBinOp (Aliases KernelsMem)) -> tps -> KernelBody (Aliases KernelsMem) -> (Names, LastUseMap, UsedNames)
segOpHelper lu_map used_names lvl binops tps body =
  let (lu_map', used_names') = foldr analyseSegBinOp (lu_map, used_names) binops
      (lu_map'', used_names'') = analyseKernelBody (lu_map', used_names') body
      nms = (freeIn lvl <> freeIn tps) `namesSubtract` used_names''
   in (nms, lu_map'', used_names'' <> nms)

analyseKernelBody :: (LastUseMap, UsedNames) -> KernelBody (Aliases KernelsMem) -> (LastUseMap, UsedNames)
analyseKernelBody (lu_map, used_names) (KernelBody dec stms result) =
  let used_names' = used_names <> freeIn result <> freeIn dec
      (lu_map', used_names'') = foldr analyseStm (lu_map, used_names) $ stmsToList stms
   in (lu_map <> lu_map', used_names' <> used_names'')

analyseSegBinOp :: SegBinOp (Aliases KernelsMem) -> (LastUseMap, UsedNames) -> (LastUseMap, UsedNames)
analyseSegBinOp (SegBinOp _ lambda neutral shp) (lu_map, used_names) =
  let (lu_map', used_names') = analyseLambda (lu_map, used_names) lambda
      nms = (freeIn neutral <> freeIn shp) `namesSubtract` used_names'
   in (lu_map', used_names' <> nms)

analyseHistOp :: HistOp (Aliases KernelsMem) -> (LastUseMap, UsedNames) -> (LastUseMap, UsedNames)
analyseHistOp (HistOp width race dest neutral shp lambda) (lu_map, used_names) =
  let (lu_map', used_names') = analyseLambda (lu_map, used_names) lambda
      nms = (freeIn width <> freeIn race <> freeIn dest <> freeIn neutral <> freeIn shp) `namesSubtract` used_names'
   in (lu_map', used_names' <> nms)

analyseLambda :: (LastUseMap, UsedNames) -> Lambda (Aliases KernelsMem) -> (LastUseMap, UsedNames)
analyseLambda (lu_map, used_names) (Lambda params body ret) =
  let (lu_map', used_names') = analyseBody lu_map used_names body
      used_names'' = used_names' <> freeIn params <> freeIn ret
   in (lu_map', used_names'')
