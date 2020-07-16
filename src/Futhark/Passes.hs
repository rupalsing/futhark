{-# LANGUAGE FlexibleContexts #-}
-- | Optimisation pipelines.
module Futhark.Passes
  ( standardPipeline
  , sequentialPipeline
  , kernelsPipeline
  , sequentialCpuPipeline
  , gpuPipeline
  )
where

import Control.Category ((>>>))

import Futhark.Optimise.CSE
import Futhark.Optimise.Fusion
import Futhark.Optimise.InPlaceLowering
import Futhark.Optimise.InliningDeadFun
import Futhark.Optimise.Sink
import Futhark.Optimise.TileLoops
import Futhark.Optimise.DoubleBuffer
import Futhark.Optimise.ReuseAllocations
import Futhark.Optimise.Unstream
import Futhark.Pass.ExpandAllocations
import qualified Futhark.Pass.ExplicitAllocations.Kernels as Kernels
import qualified Futhark.Pass.ExplicitAllocations.Seq as Seq
import Futhark.Pass.ExtractKernels
import Futhark.Pass.FirstOrderTransform
import Futhark.Pass.KernelBabysitting
import Futhark.Pass.Simplify
import Futhark.Pipeline
import Futhark.IR.KernelsMem (KernelsMem)
import Futhark.IR.SeqMem (SeqMem)
import Futhark.IR.Kernels (Kernels)
import Futhark.IR.Seq (Seq)
import Futhark.IR.SOACS (SOACS)

standardPipeline :: Pipeline SOACS SOACS
standardPipeline =
  passes [ simplifySOACS
         , inlineFunctions
         , simplifySOACS
         , performCSE True
         , simplifySOACS
           -- We run fusion twice
         , fuseSOACs
         , performCSE True
         , simplifySOACS
         , fuseSOACs
         , performCSE True
         , simplifySOACS
         , removeDeadFunctions
         ]

kernelsPipeline :: Pipeline SOACS Kernels
kernelsPipeline =
  standardPipeline >>>
  onePass extractKernels >>>
  passes [ simplifyKernels
         , babysitKernels
         , tileLoops
         , unstream
         , performCSE True
         , simplifyKernels
         , sink
         , inPlaceLoweringKernels
         ]

sequentialPipeline :: Pipeline SOACS Seq
sequentialPipeline =
  standardPipeline >>>
  onePass firstOrderTransform >>>
  passes [ simplifySeq
         , inPlaceLoweringSeq
         ]

sequentialCpuPipeline :: Pipeline SOACS SeqMem
sequentialCpuPipeline =
  sequentialPipeline >>>
  onePass Seq.explicitAllocations >>>
  passes [ performCSE False
         , simplifySeqMem
         , simplifySeqMem
         ]

gpuPipeline :: Pipeline SOACS KernelsMem
gpuPipeline =
  kernelsPipeline >>>
  onePass Kernels.explicitAllocations >>>
  passes [ simplifyKernelsMem
         , performCSE False
         , simplifyKernelsMem
         , reuseAllocations
         , simplifyKernelsMem
         , doubleBuffer
         , simplifyKernelsMem
         , expandAllocations
         , simplifyKernelsMem
         ]
