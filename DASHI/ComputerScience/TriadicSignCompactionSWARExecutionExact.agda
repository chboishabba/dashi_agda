module DASHI.ComputerScience.TriadicSignCompactionSWARExecutionExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.TriadicPrefixSWARExecutionExact as PrefixSWAR
import DASHI.ComputerScience.TriadicFin27Byte256ABIExact as ABI

------------------------------------------------------------------------
-- PAID SWAR SIGN-COMPACTION / FACTORIZED ENCODE EXECUTION
--
-- Eight independent factorized symbols occupy the byte lanes of two uint64_t
-- words: support bits and positive-sign bits.  A table-free lane-parallel
-- boolean/arithmetic network computes the exact dense ABI code 0..26 in every
-- byte lane.  The exact Git blob was compiled and checked over a 27^5 core
-- product with all eight output lanes checked on every case.
--
-- This closes SWAR encode from the already-factorized support/sign carrier.
-- Raw-trit factorization and SWAR decode remain separate residuals.
------------------------------------------------------------------------

record SignCompactionSWARSourceReceipt : Set where
  constructor sign-compaction-swar-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
    packedSupportCarrier : String
    packedSignCarrier : String
    outputCarrier : String
open SignCompactionSWARSourceReceipt public

triadicSignCompactionSWARSource : SignCompactionSWARSourceReceipt
triadicSignCompactionSWARSource = sign-compaction-swar-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "triadic_sign_compact_encode_swar.c"
  "a07cf0e00114261825caf34b8e4ba7b962735c29"
  "fc54c62864bf50afbbd8391cd58a132c76be1bc6"
  "C11"
  "uint64_t with eight uint8_t support-mask lanes"
  "uint64_t with eight uint8_t positive-sign-mask lanes"
  "uint64_t with eight uint8_t dense state-code lanes"

record SignCompactionSWARExecutionReceipt : Set where
  constructor sign-compaction-swar-execution-receipt
  field
    exactSourceBlobIdentityChecked : Bool
    compiler : String
    compilerVersion : String
    compileFlags : String
    compilationSucceeded : Bool
    executionSucceeded : Bool
    lanesPerWord : Nat
    validStatesPerLane : Nat
    exhaustiveCoreProductDimensions : Nat
    exhaustiveCoreProductCases : Nat
    allEightOutputLanesCheckedPerCase : Bool
    tableFreeDenseABICodeGeneration : Bool
    signCompactionSWAR : Bool
    factorizedEncodeSWAR : Bool
    rawTritFactorizationSWAR : Bool
    fullDecodeSWAR : Bool
    SIMDEquivalent : Bool
    CUDAEquivalent : Bool
    ROCmEquivalent : Bool
    measuredPerformance : Bool
open SignCompactionSWARExecutionReceipt public

triadicSignCompactionSWARExecution : SignCompactionSWARExecutionReceipt
triadicSignCompactionSWARExecution = sign-compaction-swar-execution-receipt
  true
  "gcc"
  "14.2.0"
  "-std=c11 -O3 -Wall -Wextra -pedantic"
  true true
  8 27 5 14348907
  true true true true
  false false false false false false

priorPrefixSWAR : PrefixSWAR.PrefixSWARExecutionReceipt
priorPrefixSWAR = PrefixSWAR.triadicPrefixSWARExecution

byteABI : Set
byteABI = ABI.Byte256

record SignCompactionSWARRoadmapBoundary : Set where
  constructor sign-compaction-swar-roadmap-boundary
  field
    supportMaskSWAR : Bool
    activeCountSWAR : Bool
    prefixAddressSWAR : Bool
    signCompactionSWAR : Bool
    factorizedEncodeSWAR : Bool
    rawTritEncodeSWAR : Bool
    decodeSWAR : Bool
    completeRoundTripSWAR : Bool
open SignCompactionSWARRoadmapBoundary public

currentSignCompactionSWARRoadmapBoundary : SignCompactionSWARRoadmapBoundary
currentSignCompactionSWARRoadmapBoundary = sign-compaction-swar-roadmap-boundary
  true true true true true false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FactorizedEncodeSWARImpliesRawTritEncodeSWAR : Set where
data FactorizedEncodeSWARImpliesDecodeSWAR : Set where
data LargeExecutedProductImpliesExhaustive27Pow8 : Set where
data SWAREncodeImpliesSIMDOrGPU : Set where

data DenseABICodeImpliesPhysicalPerformance : Set where

factorizedEncodeDoesNotPayRawFactorization :
  FactorizedEncodeSWARImpliesRawTritEncodeSWAR → ⊥
factorizedEncodeDoesNotPayRawFactorization ()

encodeDoesNotPayDecode : FactorizedEncodeSWARImpliesDecodeSWAR → ⊥
encodeDoesNotPayDecode ()

coreProductDoesNotBecome27Pow8 : LargeExecutedProductImpliesExhaustive27Pow8 → ⊥
coreProductDoesNotBecome27Pow8 ()

swarEncodeDoesNotCreateSIMDOrGPU : SWAREncodeImpliesSIMDOrGPU → ⊥
swarEncodeDoesNotCreateSIMDOrGPU ()

abiCodeDoesNotCreatePerformance : DenseABICodeImpliesPhysicalPerformance → ⊥
abiCodeDoesNotCreatePerformance ()
