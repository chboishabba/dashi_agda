module DASHI.Algebra.Quantum.DimensionFixedPoint where

open import Data.Nat renaming (ℕ to Nat) using (_∸_)
open import Relation.Binary.PropositionalEquality

record DimensionFixedPointAxioms : Set₁ where
  field
    ℝ : Set
    _R^_ : ℝ → Nat → ℝ
    _R<=_ : ℝ → ℝ → Set
    _R*_ : ℝ → ℝ → ℝ
    k : ℝ
    StableFixedPoint : Nat → Set

    HolographicBound :
      ∀ D L →
        _R<=_ (L R^ D) (k R* (L R^ (D ∸ 1)))

    StabilityUnderDecimation :
      ∀ D →
        StableFixedPoint D → D ≡ 4

open DimensionFixedPointAxioms public

Bulk : (A : DimensionFixedPointAxioms) → Nat → ℝ A → ℝ A
Bulk A D L = _R^_ A L D

Boundary : (A : DimensionFixedPointAxioms) → Nat → ℝ A → ℝ A
Boundary A D L = _R^_ A L (D ∸ 1)
