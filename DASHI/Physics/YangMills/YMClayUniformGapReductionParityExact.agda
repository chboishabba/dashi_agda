{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayUniformGapReductionParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas

------------------------------------------------------------------------
-- Aristotle 2026-09-17 literal Wilson transfer-gap reduction parity.
--
-- Donor theorem families:
--   RequestProject/YangMills/Lattice/UniformGapReduction.lean
--   RequestProject/YangMills/Lattice/TransferOperatorGap.lean
--   RequestProject/YangMills/Lattice/FrontierF1F3F4.lean
--
-- On the literal Wilson physical vacuum complement the finite transfer-form
-- problem is reduced to one decorrelation estimate
--
--   |<P0 psi, P1 psi>| <= c_k ||psi||^2,
--
-- which yields the finite form gap a_k^-1 (1-c_k).
--
-- SECOND-ROUND SHARPENING:
-- A single trajectory-uniform c<1 is NOT required.  The continuum weld consumes
-- only the per-step spectral defect
--
--   Delta * a_k <= 1 - c_k.
--
-- Hence c_k -> 1 is permitted at O(a_k), provided one fixed Delta>0 satisfies
-- the defect inequality along the physical trajectory.  The literal transfer
-- operator is T = P1* P0 and the donor also exposes the equivalent phase-
-- separation statement for the two slice embeddings.
--
-- The donor checks c=0 at zero coupling uniformly in volume.  That remains a
-- diagnostic/non-vacuity result, not the interacting beta(a)->infinity
-- continuum-trajectory estimate.
------------------------------------------------------------------------

uniformGapReductionLean : Atlas.LeanTheoremArtifact
uniformGapReductionLean = Atlas.literalSU2UniformGapReductionLean

zeroCouplingUniformGapLean : Atlas.LeanTheoremArtifact
zeroCouplingUniformGapLean = Atlas.literalSU2ZeroCouplingUniformGapLean

transferOperatorGapPath : String
transferOperatorGapPath =
  "RequestProject/YangMills/Lattice/TransferOperatorGap.lean"

trajectoryDefectCompilerTheorem : String
trajectoryDefectCompilerTheorem =
  "ym_uniform_gap_of_trajectory_decorrelation / trajectory_gap_bound_of_defect"

phaseSeparationEquivalenceTheorem : String
phaseSeparationEquivalenceTheorem =
  "decorrelation_iff_phase_separated"

literalTransferOperatorDefinition : String
literalTransferOperatorDefinition = "T = P1* P0"

literalEnergyFormIdentity : String
literalEnergyFormIdentity = "q(psi,psi) = ||psi||^2 - Re<T psi,psi>"

literalWilsonGapReducedToDecorrelator : Bool
literalWilsonGapReducedToDecorrelator = true

literalWilsonGapReducedToDecorrelatorIsTrue :
  literalWilsonGapReducedToDecorrelator ≡ true
literalWilsonGapReducedToDecorrelatorIsTrue = refl

literalTransferOperatorPaymentRecorded : Bool
literalTransferOperatorPaymentRecorded = true

literalTransferOperatorPaymentRecordedIsTrue :
  literalTransferOperatorPaymentRecorded ≡ true
literalTransferOperatorPaymentRecordedIsTrue = refl

perStepSpectralDefectConditionSuffices : Bool
perStepSpectralDefectConditionSuffices = true

perStepSpectralDefectConditionSufficesIsTrue :
  perStepSpectralDefectConditionSuffices ≡ true
perStepSpectralDefectConditionSufficesIsTrue = refl

trajectoryUniformCRequired : Bool
trajectoryUniformCRequired = false

trajectoryUniformCRequiredIsFalse :
  trajectoryUniformCRequired ≡ false
trajectoryUniformCRequiredIsFalse = refl

phaseSeparationEquivalentToDecorrelatorPayment : Bool
phaseSeparationEquivalentToDecorrelatorPayment = true

phaseSeparationEquivalentToDecorrelatorPaymentIsTrue :
  phaseSeparationEquivalentToDecorrelatorPayment ≡ true
phaseSeparationEquivalentToDecorrelatorPaymentIsTrue = refl

zeroCouplingGapUniformInVolume : Bool
zeroCouplingGapUniformInVolume = true

zeroCouplingGapUniformInVolumeIsTrue :
  zeroCouplingGapUniformInVolume ≡ true
zeroCouplingGapUniformInVolumeIsTrue = refl

-- The donor compiler is paid; the interacting physical trajectory input is not.
interactingContinuumTrajectoryUniformGapProvedByDonor : Bool
interactingContinuumTrajectoryUniformGapProvedByDonor = false

interactingContinuumTrajectoryUniformGapProvedByDonorIsFalse :
  interactingContinuumTrajectoryUniformGapProvedByDonor ≡ false
interactingContinuumTrajectoryUniformGapProvedByDonorIsFalse = refl

uniformGapReductionLeanLevel : ProofLevel
uniformGapReductionLeanLevel = standardImported

transferOperatorGapLeanLevel : ProofLevel
transferOperatorGapLeanLevel = standardImported

interactingContinuumTrajectoryGapLevel : ProofLevel
interactingContinuumTrajectoryGapLevel = conditional

data UniformGapReductionLeanDonorPresent : Set where
  uniformGapReductionLeanDonorPresent : UniformGapReductionLeanDonorPresent

uniformGapReductionLeanDonorWitness : UniformGapReductionLeanDonorPresent
uniformGapReductionLeanDonorWitness = uniformGapReductionLeanDonorPresent