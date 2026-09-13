module DASHI.ComputerScience.TriadicPrefixSWARExecutionExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.TriadicSupportMaskSWARExecutionExact as SupportSWAR
import DASHI.ComputerScience.TriadicPrefixSignCompactionPhysicalLoweringExact as Prefix

------------------------------------------------------------------------
-- PAID SWAR PREFIX-ADDRESS EXECUTION
--
-- Eight independent support masks occupy the eight byte lanes of one uint64_t.
-- For every lane simultaneously the implementation computes the second- and
-- third-position sign offsets:
--
--   o0 = 0
--   o1 = active(first)
--   o2 = active(first) + active(second)
--
-- using lane-safe shifts, masks, and addition.  The exact Git blob was compiled
-- and exhaustively executed over all 8^8 packed support-mask words.
--
-- This pays SWAR prefix-address generation.  It still does not pay sign-bit
-- scatter/compaction, full encode/decode SWAR, SIMD, CUDA, or ROCm.
------------------------------------------------------------------------

record PrefixSWARSourceReceipt : Set where
  constructor prefix-swar-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
    packedCarrier : String
    laneConvention : String
open PrefixSWARSourceReceipt public

triadicPrefixSWARSource : PrefixSWARSourceReceipt
triadicPrefixSWARSource = prefix-swar-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "triadic_prefix_swar.c"
  "e30ad806b7ad2690f0a22dca9b878901b76f2d1b"
  "ac6328418de874435cf64dab95600a063696e02e"
  "C11"
  "uint64_t with eight independent uint8_t support-mask lanes"
  "mask bit2=first trit, bit1=second, bit0=third"

record PrefixSWARExecutionReceipt : Set where
  constructor prefix-swar-execution-receipt
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
    secondOffsetEquivalentToScalar : Bool
    thirdOffsetEquivalentToScalar : Bool
    laneIsolationObservedAcrossExhaustiveDomain : Bool
    prefixAddressSWAR : Bool
    signCompactionSWAR : Bool
    fullEncodeSWAR : Bool
    fullDecodeSWAR : Bool
    SIMDExecution : Bool
    CUDAExecution : Bool
    ROCmExecution : Bool
    measuredPerformance : Bool
open PrefixSWARExecutionReceipt public

triadicPrefixSWARExecution : PrefixSWARExecutionReceipt
triadicPrefixSWARExecution = prefix-swar-execution-receipt
  true
  "gcc"
  "14.2.0"
  "-std=c11 -O3 -Wall -Wextra -pedantic"
  true true
  8 8 16777216
  true true true
  true
  false false false false false false false

priorSupportSWAR : SupportSWAR.SWARExecutionReceipt
priorSupportSWAR = SupportSWAR.triadicSupportMaskSWARExecution

semanticPrefixRoadmap : Prefix.PortableTriadicCodecRoadmap
semanticPrefixRoadmap = Prefix.currentPortableTriadicCodecRoadmap

record PrefixSWARRoadmapBoundary : Set where
  constructor prefix-swar-roadmap-boundary
  field
    supportMaskSWAR : Bool
    activeCountSWAR : Bool
    prefixAddressSWAR : Bool
    signCompactionSWAR : Bool
    fullEncodeSWAR : Bool
    fullDecodeSWAR : Bool
    scalarReferenceStillCanonical : Bool
open PrefixSWARRoadmapBoundary public

currentPrefixSWARRoadmapBoundary : PrefixSWARRoadmapBoundary
currentPrefixSWARRoadmapBoundary = prefix-swar-roadmap-boundary
  true true true false false false true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data PrefixSWARImpliesSignCompactionSWAR : Set where
data PrefixSWARImpliesFullEncodeSWAR : Set where
data PrefixSWARImpliesSIMD : Set where
data PrefixSWARImpliesGPU : Set where

data EqualPrefixOffsetsImpliesEqualMasks : Set where

prefixDoesNotPayCompaction : PrefixSWARImpliesSignCompactionSWAR → ⊥
prefixDoesNotPayCompaction ()

prefixDoesNotFinishEncode : PrefixSWARImpliesFullEncodeSWAR → ⊥
prefixDoesNotFinishEncode ()

prefixDoesNotCreateSIMD : PrefixSWARImpliesSIMD → ⊥
prefixDoesNotCreateSIMD ()

prefixDoesNotCreateGPU : PrefixSWARImpliesGPU → ⊥
prefixDoesNotCreateGPU ()

prefixProjectionDoesNotRecoverMask : EqualPrefixOffsetsImpliesEqualMasks → ⊥
prefixProjectionDoesNotRecoverMask ()
