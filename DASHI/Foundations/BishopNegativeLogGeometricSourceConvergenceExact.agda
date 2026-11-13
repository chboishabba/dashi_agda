module DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact where

------------------------------------------------------------------------
-- K04d-LOG: ORIGINAL BISHOP NEGATIVE-LOG POWER SERIES CONVERGES
-- ABSOLUTELY FOR EVERY LITERAL 0 < x < 1.
--
-- No generic logarithm-inverse authority and no opaque interval
-- predicate is used. The coefficients are exactly the original
-- rational reciprocal 1/(n+1) embedded into the pinned Bishop real.
-- The independent geometric majorant uses M = rho = x, so
--
--   |x^(n+1)/(n+1)| <= x*x^n,     0 < x < 1.
--
-- Existing proof owners:
--  Bishop/Bridges; Murray and pinned viktorcsimma/bishop Sequence
--  DASHI/Analysis/BishopGeometricMajorantSeriesConvergenceExact
--  DASHI/Foundations/BishopNatRealReciprocalSquareBaselExact.
--
-- This is a genuine source-written convergence proof. It does NOT
-- infer exp_B(L(x)) = 1/(1-x), nor does it assert that the
-- independently configured Round11 negativeLogOneMinusTerm is
-- definitionally this coefficient. Both same-object steps are
-- stated separately and must be proved, not hidden in Set fields.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
open import Data.Rational.Unnormalised as Rat using (0ℚᵘ; 1ℚᵘ)
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRecip
import DASHI.Analysis.BishopGeometricMajorantSeriesConvergenceExact as Geom
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext

sourceNegativeLogTerm : R.ℝ → Nat → R.ℝ
sourceNegativeLogTerm x n =
  R._*_
    (R.pow x (suc n))
    (R._⋆ (NatRecip.reciprocalNatRational n))

sourceNegativeLogTermNonnegative :
  (x : R.ℝ) →
  R.NonNegative x →
  (n : Nat) →
  R.NonNegative (sourceNegativeLogTerm x n)
sourceNegativeLogTermNonnegative x xNonnegative n =
  RP.nonNegx,y⇒nonNegx*y
    (Seq.nonNegx⇒nonNegxⁿ (suc n) xNonnegative)
    (NatRecip.reciprocalNonnegative n)

sourceNegativeLogAbsoluteBelowGeometric :
  (x : R.ℝ) →
  R.NonNegative x →
  (n : Nat) →
  R._≤_
    (R.∣ sourceNegativeLogTerm x n ∣)
    (Geom.scaledGeometricTerm x x n)
sourceNegativeLogAbsoluteBelowGeometric x xNonnegative n =
  RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.nonNegx⇒∣x∣≃x
        (sourceNegativeLogTermNonnegative x xNonnegative n)))
    (RP.≤-respʳ-≃
      (RP.*-comm (R.pow x n) x)
      (RP.≤-respʳ-≃
        (RP.*-identityʳ (R.pow x (suc n)))
        (RP.*-monoˡ-≤-nonNeg
          (NatRecip.reciprocalAtMostOne n)
          (Seq.nonNegx⇒nonNegxⁿ (suc n) xNonnegative))))

sourceNegativeLogAbsolutelyConvergent :
  (x : R.ℝ) →
  (zeroBelow : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  Bishop.BishopAbsoluteSeriesConvergent
    (sourceNegativeLogTerm x)
sourceNegativeLogAbsolutelyConvergent x zeroBelow belowOne =
  Geom.seriesConvergentFromScaledGeometricMajorant
    (λ n → R.∣ sourceNegativeLogTerm x n ∣)
    x x
    zeroBelow belowOne
    (RP.0≤x⇒nonNegx (RP.<⇒≤ zeroBelow))
    (λ n →
      RP.≤-respˡ-≃
        (RP.≃-symm
          (RP.nonNegx⇒∣x∣≃x
            (RP.nonNeg∣x∣ (sourceNegativeLogTerm x n))))
        (sourceNegativeLogAbsoluteBelowGeometric
          x
          (RP.0≤x⇒nonNegx (RP.<⇒≤ zeroBelow))
          n))

sourceNegativeLogValue :
  (x : R.ℝ) →
  (zeroBelow : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R.ℝ
sourceNegativeLogValue x zeroBelow belowOne =
  Bishop.bishopSeriesLimit
    (sourceNegativeLogTerm x)
    (sourceNegativeLogAbsolutelyConvergent
      x zeroBelow belowOne)

sourceNegativeLogValueConverges :
  (x : R.ℝ) →
  (zeroBelow : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  Seq._ConvergesTo_
    (Seq.SeriesOf (sourceNegativeLogTerm x))
    (sourceNegativeLogValue x zeroBelow belowOne)
sourceNegativeLogValueConverges x zeroBelow belowOne =
  Bishop.bishopSeriesLimitConvergence
    (sourceNegativeLogTerm x)
    (sourceNegativeLogAbsolutelyConvergent
      x zeroBelow belowOne)

-- A SAME-OBJECT theorem for the actual selected Round11 negative-log
-- limit, when its coefficient identification and configured interval
-- membership have themselves been supplied. Those are genuinely
-- independent from convergence of the canonical coefficients above.
sourceLogValueEqualsConfiguredBishopLog :
  (dataSet : E.BishopElementaryPowerSeriesData) →
  (x : R.ℝ) →
  (zeroBelow : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  (inside : E.InOpenUnitInterval dataSet x) →
  ((n : Nat) →
    R._≃_
      (E.negativeLogOneMinusTerm dataSet x n)
      (sourceNegativeLogTerm x n)) →
  R._≃_
    (E.bishopNegativeLogOneMinus dataSet x inside)
    (sourceNegativeLogValue x zeroBelow belowOne)
sourceLogValueEqualsConfiguredBishopLog
    dataSet x zeroBelow belowOne inside termSame =
  Ext.termwiseEquivalentSeriesHaveEquivalentLimits
    termSame
    (E.bishopNegativeLogConvergence dataSet x inside)
    (sourceNegativeLogValueConverges x zeroBelow belowOne)


------------------------------------------------------------------------
-- K04d-LOG POSITIVE OWNER: THE CANONICAL LOG SERIES IS AT LEAST x.
-- The first coefficient is L_1(x)=x; every subsequent original
-- reciprocal-power coefficient is nonnegative. The PINNED Bishop
-- monotone-limit theorem, rather than an assumed monotonic-log law,
-- gives x <= L(x) and therefore 0 < L(x) for every 0<x<1.
------------------------------------------------------------------------

sourceLogPartialIncreasing :
  (x : R.ℝ) →
  R.NonNegative x →
  Seq._isIncreasing (Seq.SeriesOf (sourceNegativeLogTerm x))
sourceLogPartialIncreasing x xNonnegative n =
  RP.≤-respˡ-≃
    (RP.+-identityʳ
      (Seq.SeriesOf (sourceNegativeLogTerm x) n))
    (RP.+-monoʳ-≤
      (Seq.SeriesOf (sourceNegativeLogTerm x) n)
      (RP.nonNegx⇒0≤x
        (sourceNegativeLogTermNonnegative x xNonnegative n)))

sourceLogFirstPartialEqualsX :
  (x : R.ℝ) →
  R._≃_
    (Seq.SeriesOf (sourceNegativeLogTerm x) (suc zero))
    x
sourceLogFirstPartialEqualsX x =
  let open RP.ℝ-Solver
  in solve 1
    (λ point →
      Κ Rat.0ℚᵘ ⊕
        ((Κ Rat.1ℚᵘ ⊗ point) ⊗ Κ Rat.1ℚᵘ)
      ⊜ point)
    RP.≃-refl x

sourceNegativeLogAtLeastPoint :
  (x : R.ℝ) →
  (zeroBelow : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R._≤_
    x
    (sourceNegativeLogValue x zeroBelow belowOne)
sourceNegativeLogAtLeastPoint x zeroBelow belowOne =
  RP.≤-respˡ-≃
    (sourceLogFirstPartialEqualsX x)
    (Seq.xₙisIncreasing⇒xₙ≤limxₙ
      (sourceLogPartialIncreasing
        x (RP.0≤x⇒nonNegx (RP.<⇒≤ zeroBelow)))
      (Bishop.bishopAbsoluteSeriesConverges
        (sourceNegativeLogAbsolutelyConvergent
          x zeroBelow belowOne))
      (suc zero))

sourceNegativeLogStrictlyPositive :
  (x : R.ℝ) →
  (zeroBelow : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R._<_ R.0ℝ (sourceNegativeLogValue x zeroBelow belowOne)
sourceNegativeLogStrictlyPositive x zeroBelow belowOne =
  RP.<-≤-trans
    zeroBelow
    (sourceNegativeLogAtLeastPoint x zeroBelow belowOne)


------------------------------------------------------------------------
-- K04d-LOG: CONSTRUCTIVE MONOTONICITY OF THE ACTUAL CANONICAL
-- NEGATIVE-LOG SERIES ON 0 < x <= y < 1.
--
-- This uses no generic logarithm order axiom. Every actual signed
-- coefficient is x^(n+1)*1/(n+1). The pinned Bishop power-order
-- theorem and multiplication by a nonnegative reciprocal prove the
-- coordinate comparison. The pinned finite-sum monotonicity and
-- order closure for limits yield the same-object analytic result.
------------------------------------------------------------------------

sourceNegativeLogTermMonotone :
  (x y : R.ℝ) →
  R.NonNegative x →
  R._≤_ x y →
  (n : Nat) →
  R._≤_
    (sourceNegativeLogTerm x n)
    (sourceNegativeLogTerm y n)
sourceNegativeLogTermMonotone x y xNonnegative x≤y n =
  RP.*-monoʳ-≤-nonNeg
    (Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
      (suc n) x≤y xNonnegative)
    (NatRecip.reciprocalNonnegative n)

sourceNegativeLogPartialMonotone :
  (x y : R.ℝ) →
  R.NonNegative x →
  R._≤_ x y →
  (count : Nat) →
  R._≤_
    (Seq.SeriesOf (sourceNegativeLogTerm x) count)
    (Seq.SeriesOf (sourceNegativeLogTerm y) count)
sourceNegativeLogPartialMonotone x y xNonnegative x≤y count =
  Seq.∑₀-mono-≤
    (sourceNegativeLogTermMonotone x y xNonnegative x≤y)
    count

sourceNegativeLogMonotone :
  (x y : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (xBelowOne : R._<_ x R.1ℝ) →
  (yPositive : R._<_ R.0ℝ y) →
  (yBelowOne : R._<_ y R.1ℝ) →
  R._≤_ x y →
  R._≤_
    (sourceNegativeLogValue x xPositive xBelowOne)
    (sourceNegativeLogValue y yPositive yBelowOne)
sourceNegativeLogMonotone
    x y xPositive xBelowOne yPositive yBelowOne x≤y =
  Seq.xₙ≤yₙ⇒limxₙ≤limyₙ
    (sourceNegativeLogPartialMonotone
      x y
      (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive))
      x≤y)
    (Bishop.bishopAbsoluteSeriesConverges
      (sourceNegativeLogAbsolutelyConvergent
        x xPositive xBelowOne))
    (Bishop.bishopAbsoluteSeriesConverges
      (sourceNegativeLogAbsolutelyConvergent
        y yPositive yBelowOne))
