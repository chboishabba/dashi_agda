module DASHI.Moonshine.AbelBishopNewtonRealTrigContinuityExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP expC CONTINUITY FROM ITS ACTUAL SCALAR PRODUCERS.
--
-- expC(x+iy) = exp_B(x)cos_B(y) + i exp_B(x)sin_B(y).
-- A single actual native Bishop complex Newton trajectory has scalar
-- exp, cos and sin sequences. The original Murray Sequence product
-- convergence immediately gives continuity of the literal expC on it.
--
-- The three scalar analytic convergences are explicit original-source
-- obligations; this file DOES NOT equate abstract package fields with
-- their concrete Bishop functions.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Native
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopNewtonSelectedLimitExact as NewtonLimit
import DASHI.Moonshine.AbelBishopAnalyticNewtonContractionExact as Disk
import DASHI.Moonshine.AbelBishopNewtonExpContinuityTransportExact as Transport

originalBishopExpComplexFromThreeScalarConvergences :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  (h : Nat → Complex.BishopComplex) →
  (limit : Complex.BishopComplex) →
  BishopSequence._ConvergesTo_
    (λ n → Exp.bishopExp (Complex.re (h n)))
    (Exp.bishopExp (Complex.re limit)) →
  BishopSequence._ConvergesTo_
    (λ n → Elementary.bishopCos (Cartesian.dataSet T)
      (Complex.im (h n)))
    (Elementary.bishopCos (Cartesian.dataSet T)
      (Complex.im limit)) →
  BishopSequence._ConvergesTo_
    (λ n → Elementary.bishopSin (Cartesian.dataSet T)
      (Complex.im (h n)))
    (Elementary.bishopSin (Cartesian.dataSet T)
      (Complex.im limit)) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Native.originalBishopExpOnSeries T (h n))
    (Native.originalBishopExpOnSeries T limit)
originalBishopExpComplexFromThreeScalarConvergences
  T h limit expConverges cosConverges sinConverges =
  Completion.original-bishop-pointwise-complex-converges
    (BishopSequence.xₙyₙ→x₀y₀
      (Exp.bishopExp (Complex.re limit) , expConverges)
      (Elementary.bishopCos (Cartesian.dataSet T)
        (Complex.im limit) , cosConverges))
    (BishopSequence.xₙyₙ→x₀y₀
      (Exp.bishopExp (Complex.re limit) , expConverges)
      (Elementary.bishopSin (Cartesian.dataSet T)
        (Complex.im limit) , sinConverges))

originalBishopNewtonNativeExpFixedFromThreeScalarContinuities :
  ∀ T nz →
  (certificate : Disk.OriginalBishopAnalyticNewtonContraction T nz) →
  let
    bounds =
      Disk.originalBishopAnalyticNewtonBuildsActualStepBounds
        T nz certificate
    orbit = Newton.originalBishopNewtonOrbit T nz
    limit = NewtonLimit.originalBishopSelectedNewtonLimit T nz bounds
  in
  BishopSequence._ConvergesTo_
    (λ n → Exp.bishopExp (Complex.re (orbit n)))
    (Exp.bishopExp (Complex.re limit)) →
  BishopSequence._ConvergesTo_
    (λ n → Elementary.bishopCos (Cartesian.dataSet T)
      (Complex.im (orbit n)))
    (Elementary.bishopCos (Cartesian.dataSet T)
      (Complex.im limit)) →
  BishopSequence._ConvergesTo_
    (λ n → Elementary.bishopSin (Cartesian.dataSet T)
      (Complex.im (orbit n)))
    (Elementary.bishopSin (Cartesian.dataSet T)
      (Complex.im limit)) →
  Complex._≈C_
    (Native.originalBishopExpOnSeries T limit)
    limit
originalBishopNewtonNativeExpFixedFromThreeScalarContinuities
  T nz certificate expConverges cosConverges sinConverges =
  let
    bounds =
      Disk.originalBishopAnalyticNewtonBuildsActualStepBounds
        T nz certificate
    orbit = Newton.originalBishopNewtonOrbit T nz
    limit = NewtonLimit.originalBishopSelectedNewtonLimit T nz bounds
  in
  Transport.originalBishopNewtonLimitExpFixedFromExpContinuity
    T nz bounds
    (originalBishopExpComplexFromThreeScalarConvergences
      T orbit limit expConverges cosConverges sinConverges)
