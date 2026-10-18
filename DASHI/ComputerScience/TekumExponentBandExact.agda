module DASHI.ComputerScience.TekumExponentBandExact where

open import Agda.Builtin.Equality using (_≡_; _≢_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; ½; _*_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.ComputerScience.TekumSignificandRangeExact as Sig
import DASHI.ComputerScience.TekumTriadicScaleExact as Scale

------------------------------------------------------------------------
-- Open magnitude band occupied by an ordinary Tekum value with exponent e:
--
--   (1/2) 3^e < |T| < (3/2) 3^e.
--
-- Consecutive endpoints meet algebraically, but neither endpoint belongs to
-- either open band.  The second half of this owner promotes that local fact to
-- arbitrary positive exponent gaps by proving the band ceilings themselves
-- strictly increase under integer successor.
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

------------------------------------------------------------------------
-- Arbitrary positive exponent gaps.
------------------------------------------------------------------------

advanceExponent : Nat → ℤ → ℤ
advanceExponent zero e = e
advanceExponent (suc n) e = Scale.integerSucc (advanceExponent n e)

oneTimes : (x : ℚ) → 1ℚ * x ≡ x
oneTimes = solve-∀

oneBelowThree : 1ℚ < Sig.three
oneBelowThree = toWitness {a? = 1ℚ <? Sig.three} _

threeHalvesPositive : 0ℚ < Sig.threeHalves
threeHalvesPositive = toWitness {a? = 0ℚ <? Sig.threeHalves} _

scaleBelowSuccessor :
  (e : ℤ) →
  Scale.triadicScale e < Scale.triadicScale (Scale.integerSucc e)
scaleBelowSuccessor e
  rewrite Scale.triadicScaleSucc e
        | canonicalThreeIsSourceThree =
  subst
    (λ left → left < Sig.three * Scale.triadicScale e)
    (oneTimes (Scale.triadicScale e))
    scaled
  where
  instance
    scalePositive : Positive (Scale.triadicScale e)
    scalePositive = positive (Scale.triadicScalePositive e)

  scaled :
    1ℚ * Scale.triadicScale e
    < Sig.three * Scale.triadicScale e
  scaled =
    ℚP.*-monoʳ-<-pos (Scale.triadicScale e) oneBelowThree

bandUpperSuccStrict :
  (e : ℤ) →
  bandUpper e < bandUpper (Scale.integerSucc e)
bandUpperSuccStrict e
  rewrite Scale.triadicScaleSucc e
        | canonicalThreeIsSourceThree =
  scaled
  where
  instance
    coefficientPositive : Positive Sig.threeHalves
    coefficientPositive = positive threeHalvesPositive

  scaled :
    Sig.threeHalves * Scale.triadicScale e
    < Sig.threeHalves * (Sig.three * Scale.triadicScale e)
  scaled =
    ℚP.*-monoˡ-<-pos Sig.threeHalves (scaleBelowSuccessor e)

bandUpperAdvanceStrict :
  (n : Nat) {e : ℤ} →
  bandUpper e < bandUpper (advanceExponent (suc n) e)
bandUpperAdvanceStrict zero {e} = bandUpperSuccStrict e
bandUpperAdvanceStrict (suc n) {e} =
  ℚP.<-trans
    (bandUpperAdvanceStrict n {e = e})
    (bandUpperSuccStrict (advanceExponent (suc n) e))

bandsOrderedByPositiveGap :
  (n : Nat) {e : ℤ} {x y : ℚ} →
  InBand e x →
  InBand (advanceExponent (suc n) e) y →
  x < y
bandsOrderedByPositiveGap zero xBand yBand =
  adjacentBandsOrdered xBand yBand
bandsOrderedByPositiveGap (suc n) {e} {x} {y} xBand yBand =
  ℚP.<-trans
    (proj₂ xBand)
    (ℚP.<-trans upperToTargetLower (proj₁ yBand))
  where
  middleExponent : ℤ
  middleExponent = advanceExponent (suc n) e

  upperToMiddleUpper :
    bandUpper e < bandUpper middleExponent
  upperToMiddleUpper = bandUpperAdvanceStrict n {e = e}

  upperToTargetLower :
    bandUpper e < bandLower (advanceExponent (suc (suc n)) e)
  upperToTargetLower =
    subst
      (λ right → bandUpper e < right)
      (sym (adjacentBoundaryEquality middleExponent))
      upperToMiddleUpper

positiveGapBandsDisjoint :
  (n : Nat) {e : ℤ} {x y : ℚ} →
  InBand e x →
  InBand (advanceExponent (suc n) e) y →
  x ≢ y
positiveGapBandsDisjoint n xBand yBand =
  ℚP.<⇒≢ (bandsOrderedByPositiveGap n xBand yBand)
