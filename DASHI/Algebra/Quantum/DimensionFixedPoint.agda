module DASHI.Algebra.Quantum.DimensionFixedPoint where

open import Data.Nat renaming (ℕ to Nat) using (_∸_)
open import Relation.Binary.PropositionalEquality

postulate ℝ : Set
postulate _R^_ : ℝ -> Nat -> ℝ
postulate _R<=_ : ℝ -> ℝ -> Set
postulate _R*_ : ℝ -> ℝ -> ℝ
postulate k : ℝ
postulate StableFixedPoint : Nat -> Set

Bulk : Nat → ℝ → ℝ
Bulk D L = L R^ D

Boundary : Nat → ℝ → ℝ
Boundary D L = L R^ (D ∸ 1)

postulate
  HolographicBound :
    ∀ D L →
      Bulk D L R<= (k R* Boundary D L)

postulate
  StabilityUnderDecimation :
    ∀ D →
      StableFixedPoint D → D ≡ 4
