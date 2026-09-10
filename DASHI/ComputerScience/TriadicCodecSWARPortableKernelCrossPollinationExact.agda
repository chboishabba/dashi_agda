module DASHI.ComputerScience.TriadicCodecSWARPortableKernelCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Codec.BalancedTritBitFibre as BitFibre
import DASHI.Codec.TriadicMaskSignFactorization as MaskSign
import DASHI.Codec.TriadicCodecFactorisationCrossPollination as Factorisation
import DASHI.Codec.TriadicPAdicCodec as PAdic
import DASHI.ComputerScience.RustPortableKernelSIMDSWARBackendSnowballExact as Portable

------------------------------------------------------------------------
-- TRIADIC CODEC / SWAR / PORTABLE-KERNEL CROSS-POLLINATION
--
-- The codec already owns three distinct implementation-facing structures:
--   1. exact per-trit support/sign factorisation;
--   2. three-trit support masks with gated signs;
--   3. five-trit base-3 packing into the mathematical range 0..242 plus an
--      abstract PhysicalCodecLayout exposing mask/sign/packed-trit words.
--
-- Those are representation/layout facts.  They are good inputs to a SWAR or
-- SIMD implementation, but they are not themselves a proof that an operation
-- executes many logical lanes in one physical machine instruction.
------------------------------------------------------------------------

codecFactorisationBoundary : Factorisation.FactorisationCrossPollinationBoundary
codecFactorisationBoundary = Factorisation.canonicalFactorisationCrossPollinationBoundary

portableSIMDSWARBoundary : Portable.SIMDSWARBoundary
portableSIMDSWARBoundary = Portable.canonicalSIMDSWARBoundary

record CodecPackedWordReceipt : Set where
  constructor codec-packed-word-receipt
  field
    supportSignFactorisationExact : Bool
    threeTritMaskShapeExact : Bool
    fiveTritBase3EncoderPresent : Bool
    fiveTritMathematicalRangeFitsByteCardinality : Bool
    executableBoundedByteDecoderPaid : Bool
    physicalMaskWordLayoutTyped : Bool
    physicalSignWordLayoutTyped : Bool
    physicalPackedTritWordLayoutTyped : Bool
    machineWordWidthBound : Bool
    withinWordParallelExecutionPaid : Bool
    namedSWARImplementationPaid : Bool
open CodecPackedWordReceipt public

canonicalCodecPackedWordReceipt : CodecPackedWordReceipt
canonicalCodecPackedWordReceipt =
  codec-packed-word-receipt
    true true true true false true true true false false false

------------------------------------------------------------------------
-- Lowering relationships.
------------------------------------------------------------------------

data CodecLoweringRelation : Set where
  supportMaskMayLowerToPackedWord : CodecLoweringRelation
  signStreamMayLowerToPackedWord : CodecLoweringRelation
  base3PackMayLowerToPackedScalar : CodecLoweringRelation
  codecWordMayLowerToSIMDVector : CodecLoweringRelation
  codecBatchMayLowerToGPUPlane : CodecLoweringRelation
  codecKernelMayLowerThroughPortableBackend : CodecLoweringRelation

record CodecBackendLoweringReceipt : Set where
  constructor codec-backend-lowering-receipt
  field
    relation : CodecLoweringRelation
    representationFactPaid : Bool
    exactMachineWordCarrierPaid : Bool
    exactLaneWidthPaid : Bool
    exactInstructionPaid : Bool
    sameSemanticsAcrossLoweringsPaid : Bool
    measuredThroughputPaid : Bool
open CodecBackendLoweringReceipt public

supportMaskPackedCandidate : CodecBackendLoweringReceipt
supportMaskPackedCandidate =
  codec-backend-lowering-receipt
    supportMaskMayLowerToPackedWord
    true false false false false false

signPackedCandidate : CodecBackendLoweringReceipt
signPackedCandidate =
  codec-backend-lowering-receipt
    signStreamMayLowerToPackedWord
    true false false false false false

pack5PackedScalarCandidate : CodecBackendLoweringReceipt
pack5PackedScalarCandidate =
  codec-backend-lowering-receipt
    base3PackMayLowerToPackedScalar
    true false false false false false

codecSIMDVectorCandidate : CodecBackendLoweringReceipt
codecSIMDVectorCandidate =
  codec-backend-lowering-receipt
    codecWordMayLowerToSIMDVector
    true false false false false false

codecGPUPlaneCandidate : CodecBackendLoweringReceipt
codecGPUPlaneCandidate =
  codec-backend-lowering-receipt
    codecBatchMayLowerToGPUPlane
    true false false false false false

------------------------------------------------------------------------
-- Existing codec exact facts retained as theorem owners.
------------------------------------------------------------------------

supportSignWordCostLaw :
  (ts : List Trit) →
  BitFibre.wordBitCost ts ≡ BitFibre.length ts + BitFibre.nonZeroCount ts
supportSignWordCostLaw = BitFibre.wordBitCost-support-plus-sign

maskSignStateCountExact : MaskSign.maskSignStateCount ≡ 27
maskSignStateCountExact = MaskSign.maskSignStateCount-is-27

------------------------------------------------------------------------
-- Portable lowering witnesses.  These are target-capability relationships,
-- not claims that the existing codec has already been implemented there.
------------------------------------------------------------------------

portableCUDAReference : Portable.PortableLoweringReceipt
portableCUDAReference = Portable.cubeCLCUDA

portableROCmReference : Portable.PortableLoweringReceipt
portableROCmReference = Portable.cubeCLROCm

portableARMReference : Portable.PortableLoweringReceipt
portableARMReference = Portable.cubeCLCPUARM

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data PackedRepresentationImpliesSWARExecution : Set where
data FiveTritBytePackingImpliesOneInstructionFiveTritOperation : Set where
data SupportMaskImpliesSIMDMaskRegister : Set where
data GPUPlaneImpliesSameLaneSemanticsAsCPUWord : Set where
data PortableBackendImpliesCodecImplementedThere : Set where
data LowerLogicalBitCostImpliesHigherPhysicalThroughput : Set where

packedRepresentationDoesNotPaySWARExecution :
  PackedRepresentationImpliesSWARExecution → ⊥
packedRepresentationDoesNotPaySWARExecution ()

pack5DoesNotPaySingleInstruction :
  FiveTritBytePackingImpliesOneInstructionFiveTritOperation → ⊥
pack5DoesNotPaySingleInstruction ()

supportMaskDoesNotIdentifySIMDRegister : SupportMaskImpliesSIMDMaskRegister → ⊥
supportMaskDoesNotIdentifySIMDRegister ()

gpuPlaneDoesNotIdentifyCPUWordLanes : GPUPlaneImpliesSameLaneSemanticsAsCPUWord → ⊥
gpuPlaneDoesNotIdentifyCPUWordLanes ()

backendCapabilityDoesNotCreateCodecImplementation :
  PortableBackendImpliesCodecImplementedThere → ⊥
backendCapabilityDoesNotCreateCodecImplementation ()

logicalBitCostDoesNotPayThroughput : LowerLogicalBitCostImpliesHigherPhysicalThroughput → ⊥
logicalBitCostDoesNotPayThroughput ()

------------------------------------------------------------------------
-- Current boundary.
------------------------------------------------------------------------

record TriadicCodecSWARPortableBoundary : Set where
  constructor triadic-codec-swar-portable-boundary
  field
    existingSupportSignFactorisationReused : Bool
    existingMaskSignTripleReused : Bool
    existingPack5RepresentationReused : Bool
    existingPhysicalWordLayoutReused : Bool
    packedRepresentationIsSWARCandidate : Bool
    exactNamedSWARExecutionAlreadyProved : Bool
    portableSIMDLoweringRepresentable : Bool
    portableCUDAAndROCmLoweringsRepresentable : Bool
    portableARMVectorLoweringRepresentable : Bool
    exactCodecImplementationOnAnyPortableTargetPaid : Bool
    physicalPerformanceComparisonPaid : Bool
open TriadicCodecSWARPortableBoundary public

canonicalTriadicCodecSWARPortableBoundary : TriadicCodecSWARPortableBoundary
canonicalTriadicCodecSWARPortableBoundary =
  triadic-codec-swar-portable-boundary
    true true true true true false true true true false false
