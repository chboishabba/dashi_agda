{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalLogAtanDerivativeLimitValuesExact where

------------------------------------------------------------------------
-- ORIGINAL LOG / ATAN: ACTUAL SOURCE DERIVATIVE SERIES LIMIT VALUES.
--
-- Unlike an axiom "source derivative converges", this uses the
-- proven vendor/bishop Sequence.geometric-series-converges for
-- the LITERAL selected source finite factor derivatives of both
-- original Log and Machin atan (not a classical log/atan carrier).
--
-- For all |x|<1:
--   P'_N(x) -> (1-x)^{-1}, for the actual source log partial P_N.
-- For all |t|<=1/2:
--   A'_N(t) -> (1+t²)^{-1}, for the actual signed atan partial A_N.
--
-- This pays the DERIVATIVE SERIES CONVERGENCE leaf, but NOT
-- native derivative-of-limit interchange. The latter must be
-- derived from a uniform quotient/tail bound, not pointwise alone.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Analysis.BishopOriginalNegativeLogFiniteDerivativeExact as LogFinite
import DASHI.Analysis.BishopOriginalMachinAtanFiniteDerivativeExact as AtanFinite
import DASHI.Analysis.BishopOriginalMachinAtanDerivativeGeometricWeldExact as AtanWeld
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopSquareNonnegativeExact as Square
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan

geometricPartialIsOriginalBishopSeries :
  (q : R.ℝ) (count : Nat) →
  R._≃_
    (Geo.geometricPartial q count)
    (Seq.SeriesOf (λ k → R.pow q k) count)
geometricPartialIsOriginalBishopSeries q zero = RP.≃-refl
geometricPartialIsOriginalBishopSeries q (suc count) =
  RP.+-cong
    (geometricPartialIsOriginalBishopSeries q count)
    RP.≃-refl

originalLogFiniteDerivativeSeriesConverges :
  (x : R.ℝ) →
  (inside : R._<_ (R.∣ x ∣) R.1ℝ) →
  Seq._ConvergesTo_
    (λ count → Geo.negativeLogDerivativePolynomial x count)
    (R._⁻¹_
      (R._-_ R.1ℝ x)
      (Seq.1-r≄0 x inside))
originalLogFiniteDerivativeSeriesConverges x inside =
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      RP.≃-symm
        (geometricPartialIsOriginalBishopSeries x (suc count))})
    ((R._⁻¹_ (R._-_ R.1ℝ x)
        (Seq.1-r≄0 x inside)) ,
      Seq.geometric-series-converges inside)

-- The original atan point is constrained by the EXACT original half
-- ball; no extra analytic domain predicate is inserted.
nativeNegativeSquareInsideUnit :
  (x : R.ℝ) →
  R._≤_ (R.∣ x ∣) Half.bishopHalf →
  R._<_
    (R.∣ R.-_ (R._*_ x x) ∣)
    R.1ℝ
nativeNegativeSquareInsideUnit x insideHalf =
  let
    xx = R._*_ x x
    absMinusSquareIsSquare :
      R._≃_ (R.∣ R.-_ xx ∣) xx
    absMinusSquareIsSquare =
      RP.≃-trans
        (RP.∣-x∣≃∣x∣ {x = xx})
        (RP.nonNegx⇒∣x∣≃x
          (Square.bishopSquareNonnegative x))

    squareBelowQuarter : R._≤_ xx Half.bishopQuarter
    squareBelowQuarter =
      RP.≤-respˡ-≃
        (RP.≃-symm (Norm.absoluteSquare x))
        (Half.bishopHalfBallMagnitudeSquareBelowQuarter x insideHalf)
  in
  RP.≤-<-trans
    (RP.≤-respˡ-≃
      (RP.≃-symm absMinusSquareIsSquare)
      squareBelowQuarter)
    Atan.quarterBelowOne

originalAtanFiniteDerivativeSeriesConverges :
  (x : R.ℝ) →
  (insideHalf : R._≤_ (R.∣ x ∣) Half.bishopHalf) →
  Seq._ConvergesTo_
    (λ count → AtanFinite.sourceAtanDerivativeFinitePartial x count)
    (R._⁻¹_
      (R._-_ R.1ℝ (R.-_ (R._*_ x x)))
      (Seq.1-r≄0
        (R.-_ (R._*_ x x))
        (nativeNegativeSquareInsideUnit x insideHalf)))
originalAtanFiniteDerivativeSeriesConverges x insideHalf =
  let
    q = R.-_ (R._*_ x x)
    qInside = nativeNegativeSquareInsideUnit x insideHalf

    originalPartialIsGeometric :
      (count : Nat) →
      R._≃_
        (AtanFinite.sourceAtanDerivativeFinitePartial x count)
        (Seq.SeriesOf (λ k → R.pow q k) count)
    originalPartialIsGeometric count =
      RP.≃-trans
        (AtanWeld.originalAtanFiniteDerivedSumIsGeometricPartial x count)
        (geometricPartialIsOriginalBishopSeries q count)
  in
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      RP.≃-symm (originalPartialIsGeometric (suc count))})
    ((R._⁻¹_ (R._-_ R.1ℝ q) (Seq.1-r≄0 q qInside)) ,
      Seq.geometric-series-converges qInside)

-- Two actual selected Machin values are now fully instantiated
-- with the original source absolute-half-ball witnesses. Only
-- infinite derivative-limit interchange remains.
originalOneFifthAtanDerivativeSeriesConverges =
  originalAtanFiniteDerivativeSeriesConverges
    Atan.bishopOneFifth Atan.bishopOneFifthInsideHalf

originalOne239AtanDerivativeSeriesConverges =
  originalAtanFiniteDerivativeSeriesConverges
    Atan.bishopOneTwoHundredThirtyNinth
    Atan.bishopOneTwoHundredThirtyNinthInsideHalf
