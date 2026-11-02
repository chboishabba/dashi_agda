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
    (RP.nonNegx⇒∣x∣≃x
      (sourceNegativeLogTermNonnegative x xNonnegative n))
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
        (RP.nonNegx⇒∣x∣≃x
          (RP.nonNeg∣x∣ (sourceNegativeLogTerm x n)))
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
