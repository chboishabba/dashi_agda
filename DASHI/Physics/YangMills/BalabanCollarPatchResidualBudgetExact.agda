module DASHI.Physics.YangMills.BalabanCollarPatchResidualBudgetExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanDyadicQuantitativeRegionExact

------------------------------------------------------------------------
-- Exact integer arithmetic for the collar-commutator patch proposal.
--
-- With collar width w, the model bound is
--
--   C_E C_R (Cχ1 C∇G / w + Cχ2 C_G / w²)
--     + C_E C_R C_G δ
--     + scale/far mismatch.
--
-- The constants below are candidate normalized coefficients.  The theorem in
-- this module verifies their common Neumann budget exactly; deriving them from
-- the physical weighted Schur estimates remains fail-closed.
------------------------------------------------------------------------

candidateCollarWidth : Nat
candidateCollarWidth = 64

backgroundDenominator : Nat
backgroundDenominator = 64

commonPatchDenominatorRaw : Nat
commonPatchDenominatorRaw =
  candidateCollarWidth * candidateCollarWidth * backgroundDenominator

cutoffNumerator :
  Nat → Nat → Nat → Nat → Nat → Nat → Nat
cutoffNumerator extensionRestriction cChi1 cChi2 cGradGreen cGreen width =
  extensionRestriction
  * (cChi1 * cGradGreen * width + cChi2 * cGreen)

-- Convert cutoff/w² and background/backgroundDenominator to the common
-- denominator w² * backgroundDenominator.
patchBaseNumerator :
  Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
patchBaseNumerator extensionRestriction cChi1 cChi2 cGradGreen cGreen
    backgroundNumerator width =
  cutoffNumerator extensionRestriction cChi1 cChi2 cGradGreen cGreen width
    * backgroundDenominator
  + extensionRestriction * cGreen * backgroundNumerator * (width * width)

candidateExtensionRestriction candidateCChi1 candidateCChi2
  candidateCGradGreen candidateCGreen candidateBackgroundNumerator : Nat
candidateExtensionRestriction = 1
candidateCChi1 = 1
candidateCChi2 = 1
candidateCGradGreen = 1
candidateCGreen = 1
candidateBackgroundNumerator = 1

candidateBasePatchNumerator : Nat
candidateBasePatchNumerator =
  patchBaseNumerator
    candidateExtensionRestriction
    candidateCChi1
    candidateCChi2
    candidateCGradGreen
    candidateCGreen
    candidateBackgroundNumerator
    candidateCollarWidth

-- The bulk transition is allocated 1/16.  Interface scale mismatch and nested
-- far-tail mismatch are each allocated one further 1/64.
bulkResidualCommonNumerator : Nat
bulkResidualCommonNumerator = 64 * 64 * 4

oneSixtyFourthCommonNumerator : Nat
oneSixtyFourthCommonNumerator = candidateCollarWidth * candidateCollarWidth

boundaryResidualNumerator : Nat
boundaryResidualNumerator = candidateBasePatchNumerator

interfaceResidualNumerator : Nat
interfaceResidualNumerator =
  candidateBasePatchNumerator + oneSixtyFourthCommonNumerator

cornerResidualNumerator : Nat
cornerResidualNumerator = candidateBasePatchNumerator

nestedResidualNumerator : Nat
nestedResidualNumerator =
  candidateBasePatchNumerator + oneSixtyFourthCommonNumerator

commonResidualNumeratorRaw : Nat
commonResidualNumeratorRaw =
  bulkResidualCommonNumerator
  + (boundaryResidualNumerator
  + (interfaceResidualNumerator
  + (cornerResidualNumerator + nestedResidualNumerator)))

-- Exact normalization by the common factor 256:
--
--   57600 / 262144 = 225 / 1024.
normalizationFactor : Nat
normalizationFactor = 256

commonResidualNumerator : Nat
commonResidualNumerator = 225

commonPatchDenominator : Nat
commonPatchDenominator = 1024

rawNumeratorNormalization :
  commonResidualNumeratorRaw
  ≡ normalizationFactor * commonResidualNumerator
rawNumeratorNormalization = refl

rawDenominatorNormalization :
  commonPatchDenominatorRaw
  ≡ normalizationFactor * commonPatchDenominator
rawDenominatorNormalization = refl

collarPatchCandidateComputation :
  ltBool commonResidualNumerator commonPatchDenominator ≡ true
collarPatchCandidateComputation = refl

collarPatchCandidateStrict :
  commonResidualNumerator <N commonPatchDenominator
collarPatchCandidateStrict =
  ltBoolSound commonResidualNumerator commonPatchDenominator
    collarPatchCandidateComputation

record CollarPatchCandidateCertificate : Set where
  constructor collarPatchCertificate
  field
    collarWidth : Nat
    commonNumerator commonDenominator : Nat
    strictCommonNeumannBudget : commonNumerator <N commonDenominator

collarPatchCandidateCertificate : CollarPatchCandidateCertificate
collarPatchCandidateCertificate =
  collarPatchCertificate
    candidateCollarWidth
    commonResidualNumerator
    commonPatchDenominator
    collarPatchCandidateStrict

collarPatchArithmeticLevel : ProofLevel
collarPatchArithmeticLevel = computed

referenceFaceCornerResidualLevel : ProofLevel
referenceFaceCornerResidualLevel = machineChecked

physicalCutoffCommutatorSchurLevel : ProofLevel
physicalCutoffCommutatorSchurLevel = conditional

physicalBackgroundPatchMismatchLevel : ProofLevel
physicalBackgroundPatchMismatchLevel = conditional

physicalInterfaceScaleMismatchLevel : ProofLevel
physicalInterfaceScaleMismatchLevel = conditional

physicalNestedFarTailLevel : ProofLevel
physicalNestedFarTailLevel = conditional
