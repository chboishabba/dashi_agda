{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopFinitePowerSeriesSequentialContinuityExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: CONSTRUCTED FINITE-TERM BISHOP REAL CONTINUITY.
--
-- A finite power-series partial is an ACTUAL pinned Bishop Sequence
-- SeriesOf at each argument, not an abstract polynomial interpretation.
-- The proof uses native constant convergence, product convergence,
-- and sum convergence; it does not assume uniform convergence or
-- continuity of the completed zeta function.
--
-- For every convergent input history x_j -> x and every fixed finite
-- cutoff N, the original finite polynomial
--   P_N(x) = Σ_(k<N) coefficient(k) * pow(x,k)
-- satisfies P_N(x_j) -> P_N(x).
--
-- Attribution: Bishop and Bridges; Murray (2022), Csimma pinned
-- Bishop backend; DASHI original polynomial/Bishop series owners.
-- Source-written; exact-head Agda kernel receipt outstanding.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as R
import RealProperties as RP
import Sequence as Seq

constantConverges :
  (x : R.ℝ) →
  Seq._ConvergesTo_ (λ _ → x) x
constantConverges x =
  Seq.xₙ≃c⇒xₙ→c
    (λ {(suc _) → RP.≃-refl})

bishopPowerSequentiallyContinuous :
  (inputs : Nat → R.ℝ) →
  (target : R.ℝ) →
  Seq._ConvergesTo_ inputs target →
  (degree : Nat) →
  Seq._ConvergesTo_
    (λ j → R.pow (inputs j) degree)
    (R.pow target degree)
bishopPowerSequentiallyContinuous inputs target converges zero =
  constantConverges R.1ℝ
bishopPowerSequentiallyContinuous inputs target converges (suc degree) =
  Seq.xₙyₙ→x₀y₀
    (R.pow target degree ,
      bishopPowerSequentiallyContinuous inputs target converges degree)
    (target , converges)

finiteOriginalBishopPowerSeries :
  (coefficients : Nat → R.ℝ) →
  R.ℝ → Nat → R.ℝ
finiteOriginalBishopPowerSeries coefficients x count =
  Seq.SeriesOf
    (λ degree →
      R._*_ (coefficients degree) (R.pow x degree))
    count

bishopFinitePowerSeriesSequentiallyContinuous :
  (coefficients : Nat → R.ℝ) →
  (inputs : Nat → R.ℝ) →
  (target : R.ℝ) →
  Seq._ConvergesTo_ inputs target →
  (count : Nat) →
  Seq._ConvergesTo_
    (λ j → finiteOriginalBishopPowerSeries coefficients (inputs j) count)
    (finiteOriginalBishopPowerSeries coefficients target count)
bishopFinitePowerSeriesSequentiallyContinuous
    coefficients inputs target converges zero =
  constantConverges R.0ℝ
bishopFinitePowerSeriesSequentiallyContinuous
    coefficients inputs target converges (suc count) =
  Seq.xₙ+yₙ→x₀+y₀
    (finiteOriginalBishopPowerSeries coefficients target count ,
      bishopFinitePowerSeriesSequentiallyContinuous
        coefficients inputs target converges count)
    (R._*_ (coefficients count) (R.pow target count) ,
      Seq.xₙyₙ→x₀y₀
        (coefficients count , constantConverges (coefficients count))
        (R.pow target count ,
          bishopPowerSequentiallyContinuous
            inputs target converges count))
