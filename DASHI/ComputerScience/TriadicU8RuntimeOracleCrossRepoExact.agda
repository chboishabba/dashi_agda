module DASHI.ComputerScience.TriadicU8RuntimeOracleCrossRepoExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.TriadicFin27Byte256ABIExact as ABI
import DASHI.ComputerScience.TriadicScalarCompactCodecReferenceExact as Ref

------------------------------------------------------------------------
-- CROSS-REPO HOST-BYTE EXECUTION RECEIPT
--
-- The formal ABI remains owned in dashi_agda.  The first concrete host-byte
-- oracle lives in dashiRTX, whose repository conventions already own
-- standalone deterministic executable experiments around ternary carriers.
--
-- Source and execution are kept separate from later SWAR/SIMD/GPU claims.
------------------------------------------------------------------------

record RuntimeSourceReceipt : Set where
  constructor runtime-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    sourceRole : String
open RuntimeSourceReceipt public

triadicU8RuntimeSource : RuntimeSourceReceipt
triadicU8RuntimeSource = runtime-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "triadic_u8_codec_reference.py"
  "3fa060a9286ae2108043bdb86616df15279228ce"
  "c92976cce69cfd6b4323c793690d310ecc9cac82"
  "first concrete host-byte oracle for TriadicFin27Byte256ABIExact"

record HostExecutionReceipt : Set where
  constructor host-execution-receipt
  field
    sourceBlobIdentityChecked : Bool
    pythonVersion : String
    numpyVersion : String
    byteCarrier : String
    validStatesExhaustivelyChecked : Nat
    reservedBytesExhaustivelyRejected : Nat
    decodeEncodeRoundTripPassed : Bool
    encodeDecodeRoundTripPassed : Bool
    supportMaskChecksPassed : Bool
    activeCountChecksPassed : Bool
    prefixOffsetChecksPassed : Bool
    exactCUDAExecution : Bool
    exactROCmExecution : Bool
    exactSIMDExecution : Bool
    exactSWARExecution : Bool
    measuredPerformance : Bool
open HostExecutionReceipt public

triadicU8HostExecution : HostExecutionReceipt
triadicU8HostExecution = host-execution-receipt
  true
  "3.13.5"
  "2.3.5"
  "numpy.uint8"
  27
  229
  true true true true true
  false false false false false

------------------------------------------------------------------------
-- ABI status: this pays a concrete host uint8 carrier, not a GPU/device ABI.
------------------------------------------------------------------------

record U8RuntimeBoundary : Set where
  constructor u8-runtime-boundary
  field
    finiteReferenceCodecExact : Bool
    fin27DenseStateABIExact : Bool
    fin256ByteSizedABIExact : Bool
    concreteHostU8CarrierPaid : Bool
    exactRuntimeSourceRevisionPaid : Bool
    exactRuntimeBlobPaid : Bool
    exhaustiveHostRoundTripPaid : Bool
    reservedRegionFailClosedPaid : Bool
    rustU8BindingPaid : Bool
    cudaUint8BindingPaid : Bool
    rocmUint8BindingPaid : Bool
    crossBackendEquivalencePaid : Bool
open U8RuntimeBoundary public

currentU8RuntimeBoundary : U8RuntimeBoundary
currentU8RuntimeBoundary = u8-runtime-boundary
  true true true true true true true true
  false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data NumpyU8ImpliesRustU8 : Set where
data HostByteImpliesDeviceByte : Set where
data ExhaustiveHostRoundTripImpliesCUDAEquivalence : Set where
data SameNumericCodeImpliesSamePhysicalRepresentation : Set where

data RuntimeSourceImpliesKernelCertification : Set where

numpyU8DoesNotCreateRustBinding : NumpyU8ImpliesRustU8 → ⊥
numpyU8DoesNotCreateRustBinding ()

hostByteDoesNotCreateDeviceByte : HostByteImpliesDeviceByte → ⊥
hostByteDoesNotCreateDeviceByte ()

hostRoundTripDoesNotCreateCUDAEquivalence : ExhaustiveHostRoundTripImpliesCUDAEquivalence → ⊥
hostRoundTripDoesNotCreateCUDAEquivalence ()

sameCodeDoesNotFixPhysicalRepresentation : SameNumericCodeImpliesSamePhysicalRepresentation → ⊥
sameCodeDoesNotFixPhysicalRepresentation ()

runtimeSourceDoesNotCreateKernelCertification : RuntimeSourceImpliesKernelCertification → ⊥
runtimeSourceDoesNotCreateKernelCertification ()
