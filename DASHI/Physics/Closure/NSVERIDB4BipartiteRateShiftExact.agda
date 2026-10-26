module DASHI.Physics.Closure.NSVERIDB4BipartiteRateShiftExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNFiniteBipartiteCovarianceExact as Bip

-- For the literal bipartite normal form, adding one reference rate to
-- every interaction does not change any cross-class work. This is finite
-- cancellation, not the missing cutoff-uniform physical B4 inequality.
rateShift : ∀ {A : Set} → ℚ → (A → ℚ) → A → ℚ
rateShift shift rate x = shift + rate x

rateDifferenceShift :
  (shift r s : ℚ) →
  (shift + r) - (shift + s) ≡ r - s
rateDifferenceShift shift r s = solve (shift ∷ r ∷ s ∷ [])

rowShiftInvariant :
  ∀ {A : Set}
  (shift : ℚ) (rate work : A → ℚ)
  (left : A) (right : List A) →
  Bip.bipartiteRow (rateShift shift rate) work left right
  ≡ Bip.bipartiteRow rate work left right
rowShiftInvariant shift rate work left [] = refl
rowShiftInvariant shift rate work left (right ∷ rest) =
  cong₂ _+_
    (cong (λ x → x * (work left - work right))
      (rateDifferenceShift shift (rate left) (rate right)))
    (rowShiftInvariant shift rate work left rest)

bipartiteRateShiftInvariant :
  ∀ {A : Set}
  (shift : ℚ) (rate work : A → ℚ)
  (noncore core : List A) →
  Bip.bipartitePairSum (rateShift shift rate) work noncore core
  ≡ Bip.bipartitePairSum rate work noncore core
bipartiteRateShiftInvariant shift rate work [] core = refl
bipartiteRateShiftInvariant shift rate work (left ∷ rest) core =
  cong₂ _+_
    (rowShiftInvariant shift rate work left core)
    (bipartiteRateShiftInvariant shift rate work rest core)

-- This result applies directly to the source B4 bipartite normal form:
-- its signed defect is invariant under uniform shifts of inputMass.
-- It does NOT justify that an arbitrary mode-dependent multiplier can
-- be shifted without changing the physical viscosity or other terms.
