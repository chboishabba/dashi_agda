module DASHI.ComputerScience.TriadicCompiledScalarU8RuntimeExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.TriadicU8RuntimeOracleCrossRepoExact as Host
import DASHI.ComputerScience.TriadicFin27Byte256ABIExact as ABI

------------------------------------------------------------------------
-- FIRST COMPILED MACHINE-BYTE WITNESS
--
-- This receipt upgrades the host-byte lane from an interpreted numpy.uint8
-- oracle to a compiled C11 uint8_t implementation.  The source blob was
-- reconstructed exactly from GitHub, its git blob SHA matched, and that exact
-- content was compiled and executed locally.
------------------------------------------------------------------------

record CompiledScalarSourceReceipt : Set where
  constructor compiled-scalar-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
    byteCarrier : String
open CompiledScalarSourceReceipt public

triadicCompiledScalarSource : CompiledScalarSourceReceipt
triadicCompiledScalarSource = compiled-scalar-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "triadic_u8_codec_reference.c"
  "7e7ba4757036f39a5aac13837a3b56ed7e7da43c"
  "01e6c4162ec8ad455afe7a2bcaa1479517529c5b"
  "C11"
  "uint8_t"

record CompiledScalarExecutionReceipt : Set where
  constructor compiled-scalar-execution-receipt
  field
    exactSourceBlobIdentityChecked : Bool
    compiler : String
    compilerVersion : String
    compileFlags : String
    compilationSucceeded : Bool
    executionSucceeded : Bool
    validStatesChecked : Nat
    reservedBytesRejected : Nat
    sourceRoundTripPassed : Bool
    encodedRoundTripPassed : Bool
    supportMaskPassed : Bool
    activeCountPassed : Bool
    prefixOffsetPassed : Bool
    exactSWARPaid : Bool
    exactSIMDPaid : Bool
    exactCUDAPaid : Bool
    exactROCmPaid : Bool
    measuredPerformancePaid : Bool
open CompiledScalarExecutionReceipt public

triadicCompiledScalarExecution : CompiledScalarExecutionReceipt
triadicCompiledScalarExecution = compiled-scalar-execution-receipt
  true
  "gcc"
  "14.2.0"
  "-std=c11 -O2 -Wall -Wextra -pedantic"
  true true
  27 229
  true true true true true
  false false false false false

record RuntimeRoadmapAdvance : Set where
  constructor runtime-roadmap-advance
  field
    formalFiniteABI : Bool
    interpretedHostU8Oracle : Bool
    compiledHostU8Oracle : Bool
    exactCompiledSourceRevision : Bool
    exhaustiveCompiledRoundTrip : Bool
    swarExecutable : Bool
    simdExecutable : Bool
    cudaExecutable : Bool
    rocmExecutable : Bool
    rustExecutable : Bool
    crossBackendEquivalence : Bool
    measuredThroughput : Bool
open RuntimeRoadmapAdvance public

currentRuntimeRoadmapAdvance : RuntimeRoadmapAdvance
currentRuntimeRoadmapAdvance = runtime-roadmap-advance
  true true true true true
  false false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CompiledScalarImpliesSWAR : Set where
data CUint8ImpliesRustU8 : Set where
data HostUint8ImpliesCUDAUint8 : Set where
data ExhaustiveScalarImpliesBackendEquivalence : Set where

data CompilerSuccessImpliesAgdaKernelSuccess : Set where

compiledScalarDoesNotCreateSWAR : CompiledScalarImpliesSWAR → ⊥
compiledScalarDoesNotCreateSWAR ()

cUint8DoesNotCreateRustBinding : CUint8ImpliesRustU8 → ⊥
cUint8DoesNotCreateRustBinding ()

hostUint8DoesNotCreateCUDAByte : HostUint8ImpliesCUDAUint8 → ⊥
hostUint8DoesNotCreateCUDAByte ()

scalarExhaustionDoesNotCreateBackendEquivalence : ExhaustiveScalarImpliesBackendEquivalence → ⊥
scalarExhaustionDoesNotCreateBackendEquivalence ()

compilerSuccessDoesNotCreateKernelSuccess : CompilerSuccessImpliesAgdaKernelSuccess → ⊥
compilerSuccessDoesNotCreateKernelSuccess ()
