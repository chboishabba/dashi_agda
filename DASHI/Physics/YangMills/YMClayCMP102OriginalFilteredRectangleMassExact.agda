module DASHI.Physics.YangMills.YMClayCMP102OriginalFilteredRectangleMassExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Nullary using (Dec)
open import Data.Integer.Base as Z using (+_; +≤+)
open import Data.Nat.Base using (z≤n; s≤s)
import Data.Rational.Unnormalised as Q using (_/_; 1ℚᵘ; *≤*)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFiniteFilteredCellSumExact as Mask
import DASHI.Foundations.BishopFiniteSeriesShiftScaleExact as Scale
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as Order
import DASHI.Foundations.BishopQuarterFilteredDegreeMajorantExact as Degree
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as CMP
import DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialRatioBishopExact as Mass
import Data.Nat.Base as N

-- The selected original cells, with their external monomial shift.
-- The triangle-complement identity is a separate algebraic weld.
filteredPowerRectangle :
  (S : Nat → Nat → Set) → (∀ i j → Dec (S i j)) →
  (Nat → R.ℝ) → R.ℝ → Nat → Nat → R.ℝ
filteredPowerRectangle S decide a X shift count =
  Seq.SeriesOf
    (λ i → Seq.SeriesOf
      (Mask.masked (S i) (decide i)
        (λ j → R._*_ (R._*_ (a i) (a j))
          (R.pow (R.∣ X ∣) (shift + (i + j)))))
      count)
    count

scaledRectangle :
  ∀ a q count →
  R._≃_
    (Seq.SeriesOf (λ i → Seq.SeriesOf
      (λ j → R._*_ q (R._*_ (a i) (a j))) count) count)
    (R._*_ q (Rect.rectangleSum a a count count))
scaledRectangle a q count =
  P.≃-trans
    (Ext.finiteSumCongruent
      (λ i → P.≃-trans
        (Scale.finiteSeriesScale q (λ j → R._*_ (a i) (a j)) count)
        (P.*-congˡ (Scale.finiteSeriesScale (a i) a count))) count)
    (Scale.finiteSeriesScale q (λ i → Rect.rectangleRow a a i count) count)

filteredPowerRectangleBelowOneMass :
  ∀ (S : Nat → Nat → Set) (decide : ∀ i j → Dec (S i j))
    (a : Nat → R.ℝ) (X : R.ℝ) shift count target →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  (∀ i → R.NonNegative (a i)) →
  R._≤_ (Seq.SeriesOf a count) R.1ℝ →
  (∀ i j → S i j → target N.≤ shift + (i + j)) →
  R._≤_ (filteredPowerRectangle S decide a X shift count)
    (R.pow Half.bishopQuarter target)
filteredPowerRectangleBelowOneMass S decide a X shift count target inside an mass degree =
  let q = R.pow Half.bishopQuarter target
      qn = Seq.nonNegx⇒nonNegxⁿ target
        (Degree.originalBishopQuarterNonnegativeFromModulus X inside)
      sn = Order.finiteSumNonnegative an count
      bound = Mask.maskedRectangleBound S decide
        (λ i j → R._*_ (R._*_ (a i) (a j))
          (R.pow (R.∣ X ∣) (shift + (i + j))))
        (λ i j → R._*_ q (R._*_ (a i) (a j)))
        (λ i j → P.nonNegx,y⇒nonNegx*y qn
          (P.nonNegx,y⇒nonNegx*y (an i) (an j)))
        (λ i j h → P.≤-respʳ-≃ (P.*-comm _ _)
          (P.*-monoˡ-≤-nonNeg
            (Degree.bishopQuarterDegreeMajorant X inside target
              (shift + (i + j)) (degree i j h))
            (P.nonNegx,y⇒nonNegx*y (an i) (an j))))
        count count
      squareBound = P.≤-respʳ-≃ (P.*-identityˡ R.1ℝ)
        (P.*-mono-≤ sn sn mass mass)
  in P.≤-trans (P.≤-respʳ-≃ (scaledRectangle a q count) bound)
    (P.≤-respʳ-≃ (P.*-identityʳ q)
      (P.*-monoˡ-≤-nonNeg
        (P.≤-respˡ-≃ (P.≃-symm (Rect.rectangleProduct a a count count))
          squareBound) qn))

originalAMassBelowOne : ∀ count → R._≤_ (Seq.SeriesOf CMP.aCoefficient count) R.1ℝ
originalAMassBelowOne count =
  P.≤-trans (Mass.originalAllAMassBelowSixElevenths count)
    (P.p≤q⇒p⋆≤q⋆ (+ 6 / 11) 1ℚᵘ
      (Q.*≤* (Z.+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

originalBMassBelowOne : ∀ count → R._≤_ (Seq.SeriesOf CMP.bCoefficient count) R.1ℝ
originalBMassBelowOne count =
  P.≤-trans (Mass.originalAllBMassBelowTenFiftySevenths count)
    (P.p≤q⇒p⋆≤q⋆ (+ 10 / 57) 1ℚᵘ
      (Q.*≤* (Z.+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s
        (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))
