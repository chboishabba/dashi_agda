module DASHI.Physics.YangMills.YMClayCorrelationCriterionParityValidation where

open import Agda.Builtin.Equality using (_≡_)

-- RED-first validation for the alternative F1 payment shape supplied by the
-- Aristotle Lean tranche.  The production owner is intentionally imported
-- before creation in the source-order history.
import DASHI.Physics.YangMills.YMClayCorrelationCriterionParityExact as Correlation

open Correlation

correlationCriterionDonorAvailable : Set
correlationCriterionDonorAvailable = CorrelationCriterionLeanDonorPresent

truncatedCorrelationCompilesToDecorrelator :
  truncatedCorrelationBoundImpliesTwoSliceDecorrelator ≡ true
truncatedCorrelationCompilesToDecorrelator =
  truncatedCorrelationBoundImpliesTwoSliceDecorrelatorIsTrue

uniformJointDensityCompilesToDecorrelator :
  uniformJointDensityMixingImpliesTwoSliceDecorrelator ≡ true
uniformJointDensityCompilesToDecorrelator =
  uniformJointDensityMixingImpliesTwoSliceDecorrelatorIsTrue

mixingCriterionDoesNotPayInteractingF1 :
  interactingWilsonMixingBoundProvedByDonor ≡ false
mixingCriterionDoesNotPayInteractingF1 =
  interactingWilsonMixingBoundProvedByDonorIsFalse

criterionDoesNotCreateCMP116Authority :
  correlationCriterionCreatesCMP116SourceAuthority ≡ false
criterionDoesNotCreateCMP116Authority =
  correlationCriterionCreatesCMP116SourceAuthorityIsFalse
