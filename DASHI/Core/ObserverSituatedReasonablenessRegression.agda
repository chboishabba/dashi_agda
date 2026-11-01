module DASHI.Core.ObserverSituatedReasonablenessRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ObserverSituatedReasonablenessExact as Reason

social-conformity-cannot-answer-reasonableness :
  Reason.ReasonablenessQueryAdequate → ⊥
social-conformity-cannot-answer-reasonableness =
  Reason.reasonablenessNotAdequate

observed-frequency-does-not-create-reasonableness :
  Reason.observedFrequencyAutomaticallyReasonable
    Reason.canonicalSituatedReasonablenessBoundary ≡ false
observed-frequency-does-not-create-reasonableness = refl

institutional-convention-does-not-create-reasonableness :
  Reason.institutionalConventionAutomaticallyReasonable
    Reason.canonicalSituatedReasonablenessBoundary ≡ false
institutional-convention-does-not-create-reasonableness = refl

observer-dependence-is-not-contentlessness :
  Reason.observerDependenceAutomaticallyContentless
    Reason.canonicalSituatedReasonablenessBoundary ≡ false
observer-dependence-is-not-contentlessness = refl
