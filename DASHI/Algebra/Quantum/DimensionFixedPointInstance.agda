module DASHI.Algebra.Quantum.DimensionFixedPointInstance where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Unit using (⊤; tt)

open import DASHI.Algebra.Quantum.DimensionFixedPoint

-- A fully concrete (but minimal) instance.
-- ℝ is Nat, all operations are total, and the stability predicate is D ≡ 4.
dimensionFixedPointAxioms : DimensionFixedPointAxioms
dimensionFixedPointAxioms =
  record
    { ℝ = Nat
    ; _R^_ = λ _ _ → 0
    ; _R<=_ = λ _ _ → ⊤
    ; _R*_ = λ _ _ → 0
    ; k = 0
    ; StableFixedPoint = λ D → D ≡ 4
    ; HolographicBound = λ _ _ → tt
    ; StabilityUnderDecimation = λ _ stable → stable
    }
