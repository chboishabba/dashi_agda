module DASHI.Physics.Closure.NSTriadKNCenteredSquareIntegerGapExact where

------------------------------------------------------------------------
-- PERIODIC B / NONZERO CENTERED-SQUARE DEFECT HAS A UNIT INTEGER GAP
--
-- The preceding crosswalk writes
--
--   C_E(alpha) - C_E(beta)
--     = c^2 (n_alpha - n_beta),
--
-- with n_alpha,n_beta natural squared lattice norms.  This owner proves the
-- discrete arithmetic needed by the covariance second-moment route:
--
--   |n_alpha - n_beta|_Q
--     = natAsRational(natGap n_alpha n_beta),
--
-- and if n_alpha != n_beta then
--
--   1 <= natAsRational(natGap n_alpha n_beta).
--
-- Hence every nonzero centered-square defect carries a canonical displacement
-- at least one BEFORE the embedding scale c^2 is reinserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat using (_≤_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale

natGap : Nat → Nat → Nat
natGap zero n = n
natGap (suc m) zero = suc m
natGap (suc m) (suc n) = natGap m n

natGapPositiveIfUnequal :
  (m n : Nat) →
  (m ≡ n → ⊥) →
  ModeNorm.PositiveNat (natGap m n)
natGapPositiveIfUnequal zero zero unequal =
  ⊥-elim (unequal refl)
natGapPositiveIfUnequal zero (suc n) unequal =
  ModeNorm.positive-suc n
natGapPositiveIfUnequal (suc m) zero unequal =
  ModeNorm.positive-suc m
natGapPositiveIfUnequal (suc m) (suc n) unequal =
  natGapPositiveIfUnequal m n
    (λ equality → unequal (cong suc equality))

positiveNatAtLeastOne :
  ∀ {n} → ModeNorm.PositiveNat n → suc zero Nat.≤ n
positiveNatAtLeastOne (ModeNorm.positive-suc n) =
  Nat.s≤s Nat.z≤n

natGapRational :
  Nat → Nat → ℚ
natGapRational m n = Scale.natAsRational (natGap m n)

natDifferenceAbsoluteIsGap :
  (m n : Nat) →
  ∣ Scale.natAsRational m - Scale.natAsRational n ∣
  ≡ natGapRational m n
natDifferenceAbsoluteIsGap zero zero = refl
natDifferenceAbsoluteIsGap zero (suc n) =
  let
    value = Scale.natAsRational (suc n)
    valueNN = Scale.natAsRationalNonnegative (suc n)
    asNegative :
      0ℚ - value ≡ - value
    asNegative = solve (value ∷ [])
  in
  trans
    (cong ∣_∣ asNegative)
    (trans
      (ℚP.∣-p∣≡∣p∣ value)
      (ℚP.0≤p⇒∣p∣≡p valueNN))
natDifferenceAbsoluteIsGap (suc m) zero =
  let
    value = Scale.natAsRational (suc m)
    valueNN = Scale.natAsRationalNonnegative (suc m)
    removeZero :
      value - 0ℚ ≡ value
    removeZero = solve (value ∷ [])
  in
  trans
    (cong ∣_∣ removeZero)
    (ℚP.0≤p⇒∣p∣≡p valueNN)
natDifferenceAbsoluteIsGap (suc m) (suc n) =
  let
    left = Scale.natAsRational m
    right = Scale.natAsRational n
    cancelSuccessors :
      Scale.natAsRational (suc m) - Scale.natAsRational (suc n)
      ≡ left - right
    cancelSuccessors = solve (left ∷ right ∷ [])
  in
  trans
    (cong ∣_∣ cancelSuccessors)
    (natDifferenceAbsoluteIsGap m n)

natGapRationalAtLeastOne :
  (m n : Nat) →
  (m ≡ n → ⊥) →
  1ℚ ≤ natGapRational m n
natGapRationalAtLeastOne m n unequal =
  Scale.natAsRationalMonotone
    (positiveNatAtLeastOne
      (natGapPositiveIfUnequal m n unequal))

centeredSquareIntegerGapClosed : Bool
centeredSquareIntegerGapClosed = true

centeredSquareIntegerGapUsesContinuity : Bool
centeredSquareIntegerGapUsesContinuity = false

centeredSquareIntegerGapUsesCutoff : Bool
centeredSquareIntegerGapUsesCutoff = false

clayPromotion : Bool
clayPromotion = false
