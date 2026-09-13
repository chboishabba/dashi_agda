module DASHI.ComputerScience.TriadicSupportMaskPhysicalLoweringExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Codec.TriadicMaskSignFactorization as MaskSign
import DASHI.ComputerScience.TriadicCodecSWARPortableKernelCrossPollinationExact as Codec
import DASHI.ComputerScience.IbrahimPortableComputingSecondHopCrossPollinationExact as SecondHop

------------------------------------------------------------------------
-- FIRST CONCRETE PORTABLE CODEC OPERATION
--
-- Operation: project three balanced trits to their three-bit nonzero/support
-- mask.  The exact mathematical owner already exists in TriadicMaskSign.
-- This module fixes that operation as the semantic contract and records which
-- hardware/runtime mechanisms can plausibly realize the same predicate->mask
-- shape without identifying their physical execution models.
------------------------------------------------------------------------

data SupportBit : Set where off on : SupportBit

supportBit : Trit → SupportBit
supportBit neg = on
supportBit zer = off
supportBit pos = on

supportTriple : MaskSign.Triple Trit → MaskSign.Triple SupportBit
supportTriple (MaskSign.triple a b c) =
  MaskSign.triple (supportBit a) (supportBit b) (supportBit c)

maskFromSupportBits : MaskSign.Triple SupportBit → MaskSign.Mask3
maskFromSupportBits (MaskSign.triple off off off) = MaskSign.mask000
maskFromSupportBits (MaskSign.triple off off on) = MaskSign.mask001
maskFromSupportBits (MaskSign.triple off on off) = MaskSign.mask010
maskFromSupportBits (MaskSign.triple off on on) = MaskSign.mask011
maskFromSupportBits (MaskSign.triple on off off) = MaskSign.mask100
maskFromSupportBits (MaskSign.triple on off on) = MaskSign.mask101
maskFromSupportBits (MaskSign.triple on on off) = MaskSign.mask110
maskFromSupportBits (MaskSign.triple on on on) = MaskSign.mask111

supportMask : MaskSign.Triple Trit → MaskSign.Mask3
supportMask = maskFromSupportBits ∘ supportTriple

supportMask-agrees-with-existing-codec :
  (t : MaskSign.Triple Trit) →
  supportMask t ≡ MaskSign.maskOf (MaskSign.encodeTriple t)
supportMask-agrees-with-existing-codec (MaskSign.triple neg neg neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple neg neg zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple neg neg pos) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple neg zer neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple neg zer zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple neg zer pos) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple neg pos neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple neg pos zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple neg pos pos) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer neg neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer neg zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer neg pos) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer zer neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer zer zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer zer pos) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer pos neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer pos zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple zer pos pos) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos neg neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos neg zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos neg pos) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos zer neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos zer zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos zer pos) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos pos neg) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos pos zer) = refl
supportMask-agrees-with-existing-codec (MaskSign.triple pos pos pos) = refl

------------------------------------------------------------------------
-- Backend realization receipts.
--
-- `primitiveSemanticShapeMatches` means the primary source documents a
-- predicate-to-mask or predicated-lane mechanism matching the abstract shape.
-- It does NOT mean DASHI has compiled this exact trit operation to that ISA.
------------------------------------------------------------------------

data PhysicalLoweringKind : Set where
  packedWordSWAR x86SIMD armNeon armSVE cudaWarpBallot rocmWaveBallot : PhysicalLoweringKind

record SupportMaskLoweringReceipt : Set where
  constructor support-mask-lowering-receipt
  field
    lowering : PhysicalLoweringKind
    primaryOwner : String
    primaryLocator : String
    primitiveSemanticShapeMatches : Bool
    exactDASHIExecutableBinding : Bool
    exactInstructionSequencePaid : Bool
    exactLaneOrVectorWidthPaid : Bool
    sameThreeTritSemanticsPaid : Bool
    measuredLatencyPaid : Bool
    measuredEnergyPaid : Bool
open SupportMaskLoweringReceipt public

swarSupportMaskCandidate : SupportMaskLoweringReceipt
swarSupportMaskCandidate = support-mask-lowering-receipt
  packedWordSWAR
  "DASHI codec substrate"
  "TriadicMaskSignFactorization + TriadicCodecSWARPortableKernelCrossPollinationExact"
  true false false false true false false

x86SupportMaskCandidate : SupportMaskLoweringReceipt
x86SupportMaskCandidate = support-mask-lowering-receipt
  x86SIMD
  "Intel"
  "Intel C++ Intrinsics Reference: _mm_movemask_epi8 extracts one selected bit from each 8-bit lane into a scalar mask"
  true false false false false false false

neonSupportMaskCandidate : SupportMaskLoweringReceipt
neonSupportMaskCandidate = support-mask-lowering-receipt
  armNeon
  "Arm"
  "Arm Neon / Advanced SIMD primary documentation; fixed-width packed SIMD"
  true false false true false false false

sveSupportMaskCandidate : SupportMaskLoweringReceipt
sveSupportMaskCandidate = support-mask-lowering-receipt
  armSVE
  "Arm"
  "Introduction to SVE; predicate registers and vector-length-agnostic predication"
  true false false false false false false

cudaSupportMaskCandidate : SupportMaskLoweringReceipt
cudaSupportMaskCandidate = support-mask-lowering-receipt
  cudaWarpBallot
  "NVIDIA"
  "CUDA Programming Guide __ballot_sync: nth result bit is predicate of nth participating warp lane"
  true false false true false false false

rocmSupportMaskCandidate : SupportMaskLoweringReceipt
rocmSupportMaskCandidate = support-mask-lowering-receipt
  rocmWaveBallot
  "AMD"
  "HIP C++ language extensions __ballot/__ballot_sync: nth result bit contains predicate from nth participating lane"
  true false false false false false false

------------------------------------------------------------------------
-- Physical residuals discovered by attempting to lower one semantic object.
------------------------------------------------------------------------

record SupportMaskPhysicalResidual : Set where
  constructor support-mask-physical-residual
  field
    semanticOperationFixed : Bool
    lanePredicateFixed : Bool
    outputMaskOrderingFixed : Bool
    backendLaneNumberingNeeded : Bool
    inactiveLanePolicyNeeded : Bool
    vectorLengthContractNeeded : Bool
    scalarMaskPackingConventionNeeded : Bool
    exactCompilerLoweringNeeded : Bool
    benchmarkNeededForPerformanceClaim : Bool
open SupportMaskPhysicalResidual public

cudaResidual : SupportMaskPhysicalResidual
cudaResidual = support-mask-physical-residual
  true true true true true true false true true

rocmResidual : SupportMaskPhysicalResidual
rocmResidual = support-mask-physical-residual
  true true true true true true false true true

sveResidual : SupportMaskPhysicalResidual
sveResidual = support-mask-physical-residual
  true true true true true true true true true

swarResidual : SupportMaskPhysicalResidual
swarResidual = support-mask-physical-residual
  true true true true false true true true true

------------------------------------------------------------------------
-- WrongType firewalls exposed by the concrete operation.
------------------------------------------------------------------------

data PredicateMaskShapeImpliesSamePhysicalMechanism : Set where
data BallotImpliesCodecKernelImplemented : Set where
data FixedThreeBitMaskImpliesFixedVectorWidth : Set where
data SVEVectorLengthImpliesMaskBitOrdering : Set where
data SIMDMaskImpliesSWARWordOperation : Set where
data SameSupportMaskImpliesSamePerformance : Set where

predicateShapeDoesNotIdentifyMechanism : PredicateMaskShapeImpliesSamePhysicalMechanism → ⊥
predicateShapeDoesNotIdentifyMechanism ()

ballotDoesNotCreateCodecKernel : BallotImpliesCodecKernelImplemented → ⊥
ballotDoesNotCreateCodecKernel ()

threeBitMaskDoesNotFixVectorWidth : FixedThreeBitMaskImpliesFixedVectorWidth → ⊥
threeBitMaskDoesNotFixVectorWidth ()

sveWidthDoesNotFixMaskOrdering : SVEVectorLengthImpliesMaskBitOrdering → ⊥
sveWidthDoesNotFixMaskOrdering ()

simdMaskDoesNotBecomeSWAR : SIMDMaskImpliesSWARWordOperation → ⊥
simdMaskDoesNotBecomeSWAR ()

sameMaskDoesNotPayPerformance : SameSupportMaskImpliesSamePerformance → ⊥
sameMaskDoesNotPayPerformance ()

------------------------------------------------------------------------
-- Cross-pollination anchors.
------------------------------------------------------------------------

existingCodecBoundary : Codec.TriadicCodecSWARPortableBoundary
existingCodecBoundary = Codec.canonicalTriadicCodecSWARPortableBoundary

secondHopBoundary : SecondHop.PortableComputingSecondHopCrossPollinationBoundary
secondHopBoundary = SecondHop.canonicalPortableComputingSecondHopCrossPollinationBoundary

record TriadicSupportMaskPhysicalLoweringBoundary : Set where
  constructor triadic-support-mask-physical-lowering-boundary
  field
    exactCodecSemanticContractPaid : Bool
    existingMaskOwnerReused : Bool
    firstConcretePortableOperationSelected : Bool
    cudaBallotShapeSourcePaid : Bool
    rocmBallotShapeSourcePaid : Bool
    armPredicateShapeSourcePaid : Bool
    x86MaskExtractionSourcePaid : Bool
    exactNamedSWARExecutionPaid : Bool
    exactCrossBackendExecutableBindingPaid : Bool
    physicalPerformanceComparisonPaid : Bool
open TriadicSupportMaskPhysicalLoweringBoundary public

canonicalTriadicSupportMaskPhysicalLoweringBoundary :
  TriadicSupportMaskPhysicalLoweringBoundary
canonicalTriadicSupportMaskPhysicalLoweringBoundary =
  triadic-support-mask-physical-lowering-boundary
    true true true true true true true false false false
