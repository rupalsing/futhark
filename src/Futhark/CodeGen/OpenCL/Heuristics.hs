-- | Some OpenCL platforms have a SIMD/warp/wavefront-based execution
-- model that execute groups of threads in lockstep, permitting us to
-- perform cross-thread synchronisation within each such group without
-- the use of barriers.  Unfortunately, there seems to be no reliable
-- way to query these sizes at runtime.  Instead, we use builtin
-- tables to figure out which size we should use for a specific
-- platform and device.  If nothing matches here, the wave size should
-- be set to one.
--
-- We also use this to select reasonable default group sizes and group
-- counts.
module Futhark.CodeGen.OpenCL.Heuristics
       ( SizeHeuristic (..)
       , DeviceType (..)
       , WhichSize (..)
       , DeviceInfo (..)
       , sizeHeuristicsTable
       )
       where

import Futhark.Analysis.PrimExp
import Futhark.Util.Pretty

-- | The type of OpenCL device that this heuristic applies to.
data DeviceType = DeviceCPU | DeviceGPU

-- | The value supplies by a heuristic can depend on some device
-- information.  This will be translated into a call to
-- @clGetDeviceInfo()@. Make sure to only request info that can be
-- casted to a scalar type.
newtype DeviceInfo = DeviceInfo String

instance Pretty DeviceInfo where
  ppr (DeviceInfo s) = text "device_info" <> parens (ppr s)

-- | A size that can be assigned a default.
data WhichSize = LockstepWidth | NumGroups | GroupSize | TileSize | Threshold

-- | A heuristic for setting the default value for something.
data SizeHeuristic =
    SizeHeuristic { platformName :: String
                  , deviceType :: DeviceType
                  , heuristicSize :: WhichSize
                  , heuristicValue :: PrimExp DeviceInfo
                  }

-- | All of our heuristics.
sizeHeuristicsTable :: [SizeHeuristic]
sizeHeuristicsTable =
  [ SizeHeuristic "NVIDIA CUDA" DeviceGPU LockstepWidth $ constant 32
  , SizeHeuristic "AMD Accelerated Parallel Processing" DeviceGPU LockstepWidth $ constant 32
  , SizeHeuristic "" DeviceGPU LockstepWidth $ constant 1
  -- We calculate the number of groups to aim for 1024 threads per
  -- compute unit if we also use the default group size.  This seems
  -- to perform well in practice.
  , SizeHeuristic "" DeviceGPU NumGroups $ 4 * max_compute_units
  , SizeHeuristic "" DeviceGPU GroupSize $ constant 256
  , SizeHeuristic "" DeviceGPU TileSize $ constant 32
  , SizeHeuristic "" DeviceGPU Threshold $ constant $ 32*1024

  , SizeHeuristic "" DeviceCPU LockstepWidth $ constant 1
  , SizeHeuristic "" DeviceCPU NumGroups max_compute_units
  , SizeHeuristic "" DeviceCPU GroupSize $ constant 32
  , SizeHeuristic "" DeviceCPU TileSize $ constant 4
  , SizeHeuristic "" DeviceCPU Threshold max_compute_units
  ]
  where constant = ValueExp . IntValue . Int32Value
        max_compute_units =
          LeafExp (DeviceInfo "MAX_COMPUTE_UNITS") $ IntType Int32
