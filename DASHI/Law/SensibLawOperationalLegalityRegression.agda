module DASHI.Law.SensibLawOperationalLegalityRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawOperationalLegalityExact as Op

formal-prohibition-does-not-pay-effective-prevention :
  Op.EffectivePreventionQueryAdequate → ⊥
formal-prohibition-does-not-pay-effective-prevention =
  Op.effectivePreventionNotAdequate

non-prosecution-does-not-establish-lawfulness :
  Op.nonProsecutionAutomaticallyLawful
    Op.canonicalOperationalLegalityBoundary ≡ false
non-prosecution-does-not-establish-lawfulness = refl

tolerance-does-not-establish-formal-authorisation :
  Op.toleratedConductAutomaticallyFormallyAuthorised
    Op.canonicalOperationalLegalityBoundary ≡ false
tolerance-does-not-establish-formal-authorisation = refl

non-enforcement-does-not-prove-intent :
  Op.nonEnforcementAutomaticallyEstablishesIntent
    Op.canonicalOperationalLegalityBoundary ≡ false
non-enforcement-does-not-prove-intent = refl
