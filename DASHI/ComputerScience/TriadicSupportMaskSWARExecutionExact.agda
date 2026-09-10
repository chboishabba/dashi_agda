module DASHI.ComputerScience.TriadicSupportMaskSWARExecutionExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.TriadicCompiledScalarU8RuntimeExact as Scalar
import DASHI.ComputerScience.TriadicActiveCountPhysicalLoweringExact as Active
import DASHI.ComputerScience.TriadicSupportMaskPhysicalLoweringExact as Support

------------------------------------------------------------------------
-- FIRST PAID SWAR EXECUTION COORDINATE
--
-- Eight codec support masks (0..7) occupy the eight byte lanes of one
-- uint64_t.  A lane-preserving SWAR population-count network computes all
-- eight active counts in one scalar-word dataflow.  The exact source blob was
-- compiled and exhaustively checked over all 8^8 codec-domain packed words.
--
-- This pays SWAR for support-mask active count only.  It does not yet pay
-- complete triadic encode/decode SWAR or any SIMD/CUDA/ROCm realization.
------------------------------------------------------------------------

record SWARSourceReceipt : Set where
  constructor swar-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
    packedCarrier : String
    laneCarrier : String
open SWARSourceReceipt public

triadicSupportMaskSWARSource : SWARSourceReceipt
triadicSupportMaskSWARSource = swar-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "triadic_support_mask_swar.c"
  "afabb3f3d655f3110cf130a70a3540180f4b95f0"
  "1ab8bb2cd166da4b1244c123927c514fbb9e225f"
  "C11"
  "uint64_t"
  "8 independent byte lanes carrying support masks 0..7"

record SWARExecutionReceipt : Set where
  constructor swar-execution-receipt
  field
    exactSourceBlobIdentityChecked : Bool
    compiler : String
    compilerVersion : String
    compileFlags : String
    compilationSucceeded : Bool
    executionSucceeded : Bool
    lanesPerWord : Nat
    supportStatesPerLane : Nat
    exhaustivePackedWordsChecked : Nat
    laneActiveCountEquivalentToScalar : Bool
    laneIsolationObservedAcrossExhaustiveDomain : Bool
    completeEncodeDecodeSWAR : Bool
    prefixSignAddressSWAR : Bool
    signCompactionSWAR : Bool
    SIMDExecution : Bool
    CUDAExecution : Bool
    ROCmExecution : Bool
    measuredPerformance : Bool
open SWARExecutionReceipt public

triadicSupportMaskSWARExecution : SWARExecutionReceipt
triadicSupportMaskSWARExecution = swar-execution-receipt
  true
  "gcc"
  "14.2.0"
  "-std=c11 -O3 -Wall -Wextra -pedantic"
  true true
  8 8 16777216
  true true
  false false false false false false false

record SWARRoadmapBoundary : Set where
  constructor swar-roadmap-boundary
  field
    compiledScalarCodec : Bool
    supportMaskSWAR : Bool
    activeCountSWAR : Bool
    prefixAddressSWAR : Bool
    compactSignStreamSWAR : Bool
    fullEncodeDecodeSWAR : Bool
    SIMDEquivalent : Bool
    GPUEquivalent : Bool
open SWARRoadmapBoundary public

currentSWARRoadmapBoundary : SWARRoadmapBoundary
currentSWARRoadmapBoundary = swar-roadmap-boundary
  true true true false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ActiveCountSWARImpliesFullCodecSWAR : Set where
data SWARImpliesSIMD : Set where
data SWARImpliesGPU : Set where
data ExhaustiveSupportDomainImpliesEncodeDecodeDomain : Set where

data EightByteLanesImpliesHardwareSIMDLanes : Set where

activeCountSWARDoesNotFinishCodec : ActiveCountSWARImpliesFullCodecSWAR → ⊥
activeCountSWARDoesNotFinishCodec ()

swarDoesNotCreateSIMDIdentity : SWARImpliesSIMD → ⊥
swarDoesNotCreateSIMDIdentity ()

swarDoesNotCreateGPUIdentity : SWARImpliesGPU → ⊥
swarDoesNotCreateGPUIdentity ()

supportExhaustionDoesNotPayEncodeDecode : ExhaustiveSupportDomainImpliesEncodeDecodeDomain → ⊥
supportExhaustionDoesNotPayEncodeDecode ()

byteLanesDoNotCreateHardwareSIMDLanes : EightByteLanesImpliesHardwareSIMDLanes → ⊥
byteLanesDoNotCreateHardwareSIMDLanes ()
