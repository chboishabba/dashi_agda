module DASHI.Core.InstitutionalNormProductionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.InstitutionalNormProductionExact as Norm

production-history-erasure-is-a-real-defect :
  Norm.ProductionHistoryQueryAdequacyDefect
production-history-erasure-is-a-real-defect =
  Norm.productionHistoryQueryAdequacyDefect

bare-baseline-cannot-answer-production-history :
  Norm.ProductionHistoryQueryAdequate → ⊥
bare-baseline-cannot-answer-production-history =
  Norm.productionHistoryNotAdequate

retained-history-strictly-refines-baseline :
  Norm.BaselineWithHistoryStrictRefinement
retained-history-strictly-refines-baseline =
  Norm.baselineWithHistoryStrictlyRefinesBaseline

legal-validity-does-not-create-neutrality :
  Norm.legalValidityAutomaticallyPoliticalNeutrality
    Norm.canonicalInstitutionalNormProductionBoundary ≡ false
legal-validity-does-not-create-neutrality = refl

proximity-does-not-create-causation :
  Norm.proximityAutomaticallyEstablishesInfluenceCausation
    Norm.canonicalInstitutionalNormProductionBoundary ≡ false
proximity-does-not-create-causation = refl

formal-equality-does-not-pay-equal-norm-power :
  Norm.formalEqualityAutomaticallyEqualNormProductionPower
    Norm.canonicalInstitutionalNormProductionBoundary ≡ false
formal-equality-does-not-pay-equal-norm-power = refl
