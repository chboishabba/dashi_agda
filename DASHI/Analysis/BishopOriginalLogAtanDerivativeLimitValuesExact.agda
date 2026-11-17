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
open import Data.Product.Base using (proj₁)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Analysis.BishopFinitePowerSeriesSequentialContinuityExact as FiniteCont
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import DASHI.Analysis.BishopOriginalNegativeLogFiniteDerivativeExact as LogFinite
import DASHI.Analysis.BishopOriginalMachinAtanFiniteDerivativeExact as AtanFinite
import DASHI.Analysis.BishopOriginalMachinAtanDerivativeGeometricWeldExact as AtanWeld
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopSquareNonnegativeExact as Square
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan

-- Reuse the exact ORIGINAL Bishop geometric-series limit carrier.
-- The vendor inverse's nonzero witness is intentionally private;
-- its convergent pair already contains the correct computed inverse.
-- Projecting that same pair avoids any synthetic inverse witness.
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
    (proj₁ (Seq.geometric-series-isConvergent inside))
originalLogFiniteDerivativeSeriesConverges x inside =
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      RP.≃-symm
        (geometricPartialIsOriginalBishopSeries x (suc count))})
    (Seq.geometric-series-isConvergent inside)

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
        (Norm.absoluteSquare x)
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
    (proj₁ (Seq.geometric-series-isConvergent
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
    (Seq.geometric-series-isConvergent qInside)

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

------------------------------------------------------------------------
-- EXACT INFINITE GEOMETRIC DERIVATIVE CANCELLATION.
--
-- This is the actual pinned-Bishop convergence of BOTH sides of
-- (1-q) P_N(q) = 1-q^N. It is NOT a formal coefficient calculation.
-- The limit is uniquely characterized by the original Sequence.lim
-- used by the actual finite source log and atan derivative series.
------------------------------------------------------------------------

originalGeometricDerivativeLimitCancels :
  (q : R.ℝ) →
  (inside : R._<_ (R.∣ q ∣) R.1ℝ) →
  R._≃_
    (R._*_
      (R._-_ R.1ℝ q)
      (proj₁ (Seq.geometric-series-isConvergent inside)))
    R.1ℝ
originalGeometricDerivativeLimitCancels q inside =
  let
    factor = R._-_ R.1ℝ q
    selectedLimit = proj₁ (Seq.geometric-series-isConvergent inside)

    constantFactorConverges :
      Seq._ConvergesTo_ (λ _ → factor) factor
    constantFactorConverges =
      FiniteCont.constantConverges factor

    sourceDerivativePartialConverges :
      Seq._ConvergesTo_
        (λ n → Geo.geometricPartial q n)
        selectedLimit
    sourceDerivativePartialConverges =
      originalLogFiniteDerivativeSeriesConverges q inside

    finiteProductsConverge :
      Seq._ConvergesTo_
        (λ n → R._*_ factor (Geo.geometricPartial q n))
        (R._*_ factor selectedLimit)
    finiteProductsConverge =
      Seq.xₙyₙ→x₀y₀
        (factor , constantFactorConverges)
        (selectedLimit , sourceDerivativePartialConverges)

    telescopeSideConverges :
      Seq._ConvergesTo_
        (λ n → R._-_ R.1ℝ (R.pow q n))
        (R._*_ factor selectedLimit)
    telescopeSideConverges =
      Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) →
          Geo.geometricPolynomialTelescope q (suc n)})
        (R._*_ factor selectedLimit , finiteProductsConverge)

    powersConvergeZero :
      Seq._ConvergesTo_
        (λ n → R.pow q n)
        R.0ℝ
    powersConvergeZero = Seq.∣r∣<1⇒rⁿ→0 inside

    oneMinusPowersConvergesOne :
      Seq._ConvergesTo_
        (λ n → R._-_ R.1ℝ (R.pow q n))
        R.1ℝ
    oneMinusPowersConvergesOne =
      Seq.xₙ→x∧x≃y⇒xₙ→y
        (Seq.xₙ+yₙ→x₀+y₀
          (R.1ℝ , FiniteCont.constantConverges R.1ℝ)
          (R.-_ R.0ℝ ,
            Seq.-xₙ→-x₀ (R.0ℝ , powersConvergeZero)))
        (let open RP.ℝ-Solver in
         solve 0
           (Κ 1ℚᵘ ⊕ (⊝ Κ 0ℚᵘ) ⊜ Κ 1ℚᵘ)
           RP.≃-refl)
  in
  Seq.uniqueness-of-limits
    telescopeSideConverges
    oneMinusPowersConvergesOne

-- This is the ORIGINAL source negative-log derivative partial limit:
-- no newly selected inverse or derivative-value oracle.
originalLogSourceDerivativeLimitIsReciprocal :
  (x : R.ℝ) →
  (inside : R._<_ (R.∣ x ∣) R.1ℝ) →
  R._≃_
    (R._*_
      (R._-_ R.1ℝ x)
      (proj₁ (Seq.geometric-series-isConvergent inside)))
    R.1ℝ
originalLogSourceDerivativeLimitIsReciprocal =
  originalGeometricDerivativeLimitCancels

-- The two original Machin points instantiate the same actual
-- geometric derivative limit with q=-x*x; the factor is 1+x*x.
originalAtanSourceDerivativeLimitIsReciprocal :
  (x : R.ℝ) →
  (insideHalf : R._≤_ (R.∣ x ∣) Half.bishopHalf) →
  let q = R.-_ (R._*_ x x)
      inside = nativeNegativeSquareInsideUnit x insideHalf
  in
  R._≃_
    (R._*_
      (R._+_ R.1ℝ (R._*_ x x))
      (proj₁ (Seq.geometric-series-isConvergent inside)))
    R.1ℝ
originalAtanSourceDerivativeLimitIsReciprocal x insideHalf =
  let
    q = R.-_ (R._*_ x x)
    inside = nativeNegativeSquareInsideUnit x insideHalf
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.*-cong
      (solve 1
        (λ y → Κ 1ℚᵘ ⊕ y ⊜ Κ 1ℚᵘ ⊖ (⊝ y))
        RP.≃-refl (R._*_ x x))
      RP.≃-refl)
    (originalGeometricDerivativeLimitCancels q inside)

originalOneFifthDerivativeLimitCancels :
  let x = Atan.bishopOneFifth
      inside = nativeNegativeSquareInsideUnit
        x Atan.bishopOneFifthInsideHalf
  in
  R._≃_
    (R._*_
      (R._+_ R.1ℝ (R._*_ x x))
      (proj₁ (Seq.geometric-series-isConvergent inside)))
    R.1ℝ
originalOneFifthDerivativeLimitCancels =
  originalAtanSourceDerivativeLimitIsReciprocal
    Atan.bishopOneFifth Atan.bishopOneFifthInsideHalf

originalOne239DerivativeLimitCancels :
  let x = Atan.bishopOneTwoHundredThirtyNinth
      inside = nativeNegativeSquareInsideUnit
        x Atan.bishopOneTwoHundredThirtyNinthInsideHalf
  in
  R._≃_
    (R._*_
      (R._+_ R.1ℝ (R._*_ x x))
      (proj₁ (Seq.geometric-series-isConvergent inside)))
    R.1ℝ
originalOne239DerivativeLimitCancels =
  originalAtanSourceDerivativeLimitIsReciprocal
    Atan.bishopOneTwoHundredThirtyNinth
    Atan.bishopOneTwoHundredThirtyNinthInsideHalf
