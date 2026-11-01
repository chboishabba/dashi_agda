module DASHI.Algebra.QuantumInterface where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (¬_)

-- Abstract state space + observable/entropy-like measure
record QuantumSys (ℓ : Level) : Set (lsuc ℓ) where
  field
    QState : Set ℓ
    step   : QState → QState

    -- “Unitary-like” = invertible evolution
    inv    : QState → QState
    left   : ∀ s → inv (step s) ≡ s
    right  : ∀ s → step (inv s) ≡ s

    -- Measurement/projection (can be non-invertible)
    meas   : QState → QState
    meas-idem : ∀ s → meas (meas s) ≡ meas s

    -- Any scalar you use as “entropy / action / code length”
    H      : QState → Set ℓ  -- keep general; specialize to Nat later
