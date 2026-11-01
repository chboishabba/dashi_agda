module DASHI.Physics.Closure.Projection where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

-- First-class execution-side projection object. The contract consumes an
-- explicit projected observable carrier together with a compatibility law for
-- projected deltas instead of leaving projection as an informal convention.
record Projection
  {ℓx ℓπ ℓδx ℓδπ : Level}
  (State : Set ℓx)
  (Source : Set ℓπ)
  (ΔState : Set ℓδx)
  (ΔSource : Set ℓδπ)
  : Set (lsuc (ℓx ⊔ ℓπ ⊔ ℓδx ⊔ ℓδπ)) where
  field
    π : State → Source
    Δ : State → State → ΔState
    projectΔ : ΔState → ΔSource
    Δπ : Source → Source → ΔSource

    projected-delta-compatible :
      ∀ x y →
      projectΔ (Δ x y) ≡ Δπ (π x) (π y)

open Projection public
