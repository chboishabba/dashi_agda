{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayCorrelationCriterionParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas

------------------------------------------------------------------------
-- Aristotle 2026-09-17 connected-correlation / uniform-mixing F1 criterion.
--
-- Donor file:
--   RequestProject/YangMills/Lattice/CorrelationCriterion.lean
--
-- The Lean tranche proves two compiler statements on the literal Wilson slice
-- objects:
--
--   connected/truncated two-slice correlation bound
--     -> |<P0 psi,P1 psi>| <= c ||psi||^2,
--
-- and the stronger sufficient condition
--
--   joint two-slice law = (1+h) * (product of slice marginals), |h| <= eps
--     -> |<P0 psi,P1 psi>| <= eps ||psi||^2.
--
-- The first is the constructive-QFT connected-correlation normal form of the
-- transfer estimate.  The second isolates a classical mixing/density estimate
-- of exactly the kind a convergent polymer/cluster expansion may supply.
--
-- AUTHORITY BOUNDARY:
-- This owner records verified Lean theorem artifacts and the logical reduction.
-- It does NOT prove the interacting Wilson density/mixing hypothesis along the
-- continuum trajectory; it does NOT import CMP116 source authority; and it does
-- not identify a generic mixing kernel with Bałaban's source-localization ABI.
------------------------------------------------------------------------

correlationCriterionLean : Atlas.LeanTheoremArtifact
correlationCriterionLean = Atlas.literalSU2CorrelationCriterionLean

correlationCriterionPath : String
correlationCriterionPath =
  "RequestProject/YangMills/Lattice/CorrelationCriterion.lean"

truncatedCorrelationTheorem : String
truncatedCorrelationTheorem =
  "decorrelation_of_truncated_correlation"

uniformJointDensityTheorem : String
uniformJointDensityTheorem =
  "decorrelation_of_uniform_joint_density"

literalSliceNormIdentityTheorem : String
literalSliceNormIdentityTheorem =
  "integral_norm_sq_slice"

truncatedCorrelationBoundImpliesTwoSliceDecorrelator : Bool
truncatedCorrelationBoundImpliesTwoSliceDecorrelator = true

truncatedCorrelationBoundImpliesTwoSliceDecorrelatorIsTrue :
  truncatedCorrelationBoundImpliesTwoSliceDecorrelator ≡ true
truncatedCorrelationBoundImpliesTwoSliceDecorrelatorIsTrue = refl

uniformJointDensityMixingImpliesTwoSliceDecorrelator : Bool
uniformJointDensityMixingImpliesTwoSliceDecorrelator = true

uniformJointDensityMixingImpliesTwoSliceDecorrelatorIsTrue :
  uniformJointDensityMixingImpliesTwoSliceDecorrelator ≡ true
uniformJointDensityMixingImpliesTwoSliceDecorrelatorIsTrue = refl

vacuumOrthogonalityRemovesDisconnectedTerm : Bool
vacuumOrthogonalityRemovesDisconnectedTerm = true

vacuumOrthogonalityRemovesDisconnectedTermIsTrue :
  vacuumOrthogonalityRemovesDisconnectedTerm ≡ true
vacuumOrthogonalityRemovesDisconnectedTermIsTrue = refl

uniformDensityCriterionIsOperatorFreePhysicalInputShape : Bool
uniformDensityCriterionIsOperatorFreePhysicalInputShape = true

uniformDensityCriterionIsOperatorFreePhysicalInputShapeIsTrue :
  uniformDensityCriterionIsOperatorFreePhysicalInputShape ≡ true
uniformDensityCriterionIsOperatorFreePhysicalInputShapeIsTrue = refl

-- The theorem is a compiler from a mixing hypothesis to the existing transfer
-- decorrelator payment.  The physical hypothesis itself remains open at the
-- interacting continuum trajectory.
interactingWilsonMixingBoundProvedByDonor : Bool
interactingWilsonMixingBoundProvedByDonor = false

interactingWilsonMixingBoundProvedByDonorIsFalse :
  interactingWilsonMixingBoundProvedByDonor ≡ false
interactingWilsonMixingBoundProvedByDonorIsFalse = refl

correlationCriterionCreatesCMP116SourceAuthority : Bool
correlationCriterionCreatesCMP116SourceAuthority = false

correlationCriterionCreatesCMP116SourceAuthorityIsFalse :
  correlationCriterionCreatesCMP116SourceAuthority ≡ false
correlationCriterionCreatesCMP116SourceAuthorityIsFalse = refl

correlationCriterionIsAlternateF1ProducerShape : Bool
correlationCriterionIsAlternateF1ProducerShape = true

correlationCriterionIsAlternateF1ProducerShapeIsTrue :
  correlationCriterionIsAlternateF1ProducerShape ≡ true
correlationCriterionIsAlternateF1ProducerShapeIsTrue = refl

correlationCriterionLeanLevel : ProofLevel
correlationCriterionLeanLevel = standardImported

interactingWilsonMixingInputLevel : ProofLevel
interactingWilsonMixingInputLevel = conditional

data CorrelationCriterionLeanDonorPresent : Set where
  correlationCriterionLeanDonorPresent : CorrelationCriterionLeanDonorPresent

correlationCriterionLeanDonorWitness : CorrelationCriterionLeanDonorPresent
correlationCriterionLeanDonorWitness = correlationCriterionLeanDonorPresent
