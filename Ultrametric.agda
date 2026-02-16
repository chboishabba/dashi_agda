module Ultrametric where

open import Data.Nat using (ℕ; _≤_; _<_)
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Data.Nat using (ℕ; _⊔_)
max : ℕ → ℕ → ℕ
max = _⊔_


------------------------------------------------------------------------
-- Distance function into ℕ (discrete ultrametric)

record Ultrametric (S : Set) : Set₁ where
  field
    d : S → S → Nat

    -- Identity
    id-zero :
      ∀ x → d x x ≡ 0

    -- Symmetry
    symmetric :
      ∀ x y → d x y ≡ d y x

    -- Strong triangle inequality (ultrametric)
    ultratriangle :
      ∀ x y z →
      d x z ≤ max (d x y) (d y z)
