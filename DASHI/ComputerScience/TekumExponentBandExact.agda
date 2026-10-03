module DASHI.ComputerScience.TekumExponentBandExact where

open import Agda.Builtin.Equality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; ½; _*_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.ComputerScience.TekumSignificandRangeExact as Sig
import DASHI.ComputerScience.TekumTriadicScaleExact as Scale

------------------------------------------------------------------------
-- Open magnitude band occupied by an ordinary Tekum value with exponent e:
--
--   (1/2) 3^e < |T| < (3/2) 3^e.
--
-- This owner first proves that consecutive bands are strictly ordered.  The
-- endpoints meet algebraically, but neither endpoint belongs to either band.
------------------------------------------------------------------------

bandLower : ℤ → ℚ
bandLower e = ½ * Scale.triadicScale e

bandUpper : ℤ → ℚ
bandUpper e = Sig.threeHalves * Scale.triadicScale e

halfPositive : ℚ.Positive ½
halfPositive = _

bandLowerPositive :
  (e : ℤ) → 0ℚ < bandLower e
bandLowerPositive e =
  let instance halfPositiveInstance = halfPositive
  in ℚP.*-monoʳ-<-pos ½ (Scale.triadicScalePositive e)

halfThreeScale :
  (s : ℚ) →
  ½ * (Sig.three * s) ≡ Sig.threeHalves * s
halfThreeScale = solve-∀

canonicalThreeIsSourceThree :
  Scale.canonicalThree ≡ Sig.three
canonicalThreeIsSourceThree = refl

adjacentBoundaryEquality :
  (e : ℤ) →
  bandLower (Scale.integerSucc e) ≡ bandUpper e
adjacentBoundaryEquality e
  rewrite Scale.triadicScaleSucc e
        | canonicalThreeIsSourceThree =
  halfThreeScale (Scale.triadicScale e)

InBand : ℤ → ℚ → Set
InBand e x = bandLower e < x × x < bandUpper e

adjacentBandsOrdered :
  ∀ {e x y} →
  InBand e x →
  InBand (Scale.integerSucc e) y →
  x < y
adjacentBandsOrdered {e} {x} {y} xBand yBand =
  ℚP.<-trans
    (proj₂ xBand)
    (subst
      (_< y)
      (adjacentBoundaryEquality e)
      (proj₁ yBand))

adjacentBandsDisjoint :
  ∀ {e x y} →
  InBand e x →
  InBand (Scale.integerSucc e) y →
  x ≢ y
adjacentBandsDisjoint xBand yBand =
  ℚP.<⇒≢ (adjacentBandsOrdered xBand yBand)

sameValueCannotOccupyAdjacentBands :
  ∀ {e x} →
  InBand e x →
  InBand (Scale.integerSucc e) x →
  ⊥
sameValueCannotOccupyAdjacentBands xBand nextBand =
  adjacentBandsDisjoint xBand nextBand refl
