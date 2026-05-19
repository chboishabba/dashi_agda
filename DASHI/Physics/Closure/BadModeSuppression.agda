module DASHI.Physics.Closure.BadModeSuppression where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Nat using (ℕ; _≤_)

-- Receipt-side stub for measured bad-mode suppression surfaces.
-- This stays intentionally weak: it names the observable and the intended
-- monotonicity gate after coherence, without claiming semantic impossibility.
record BadModeSurface
  {ℓs : Level}
  (State : Set ℓs)
  : Set (lsuc ℓs) where
  field
    step : State → State
    badMass : State → ℕ
    coherenceReached : State → Set

  BadMassNonIncreasingAfterCoherence : Set ℓs
  BadMassNonIncreasingAfterCoherence =
    ∀ s → coherenceReached s → badMass (step s) ≤ badMass s

open BadModeSurface public

record BadModeSuppressionContract
  {ℓs : Level}
  (State : Set ℓs)
  : Set (lsuc ℓs) where
  field
    surface : BadModeSurface State
    eventualSafeBias : Set ℓs

open BadModeSuppressionContract public
