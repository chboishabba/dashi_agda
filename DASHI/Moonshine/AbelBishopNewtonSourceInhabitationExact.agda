module DASHI.Moonshine.AbelBishopNewtonSourceInhabitationExact where

------------------------------------------------------------------------
-- FULL SOURCE-WRITTEN BISHOP NEWTON FIXED-POINT CONSUMER.
--
-- The selected point p is NOT supplied as a record field.
-- It is the canonical Bishop limit of the actual native-expC Newton
-- orbit starting from the literal rational complex center.
--
-- Source inputs still to be paid with constructive analytic proofs:
--   1. sin_B(133724/100000)>0, for the *selected* trig source;
--   2. source squared-distance Newton disk stability and contraction,
--      and first-step bound, on the SAME native operator;
--   3. continuity of the actual original Bishop exp, sin, cos
--      along that actual Newton orbit.
--
-- Derived, with NO additional hypothesis:
--   Newton denominator nonzero, all Newton step geometric bounds,
--   completed Bishop p, and expC(p)≈C p on the SAME source carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Native
import DASHI.Moonshine.AbelBishopNewtonCenterDenominatorExact as Denominator
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopNewtonSelectedLimitExact as Limit
import DASHI.Moonshine.AbelBishopAnalyticNewtonContractionExact as Disk
import DASHI.Moonshine.AbelBishopNewtonRealTrigContinuityExact as Continuity

record OriginalBishopNewtonActualAnalyticSources
    (T : Cartesian.BishopSetoidComplexTranscendentals) : Set₁ where

  field
    selectedSinePositive :
      BishopReal._<_ BishopReal.0ℝ
        (Elementary.bishopSin
          (Cartesian.dataSet T)
          Denominator.bishopNewtonCenterImag)

  private
    nz =
      Denominator.bishopNewtonDenominatorNonzeroFromOriginalSine
        T selectedSinePositive

  field
    selectedDiskCertificate :
      Disk.OriginalBishopAnalyticNewtonContraction T nz

  private
    steps =
      Disk.originalBishopAnalyticNewtonBuildsActualStepBounds
        T nz selectedDiskCertificate
    orbit = Newton.originalBishopNewtonOrbit T nz
    p = Limit.originalBishopSelectedNewtonLimit T nz steps

  field
    originalExpContinuousAlongNewton :
      BishopSequence._ConvergesTo_
        (λ n → Exp.bishopExp (Complex.re (orbit n)))
        (Exp.bishopExp (Complex.re p))

    originalCosContinuousAlongNewton :
      BishopSequence._ConvergesTo_
        (λ n → Elementary.bishopCos (Cartesian.dataSet T)
          (Complex.im (orbit n)))
        (Elementary.bishopCos (Cartesian.dataSet T)
          (Complex.im p))

    originalSinContinuousAlongNewton :
      BishopSequence._ConvergesTo_
        (λ n → Elementary.bishopSin (Cartesian.dataSet T)
          (Complex.im (orbit n)))
        (Elementary.bishopSin (Cartesian.dataSet T)
          (Complex.im p))

open OriginalBishopNewtonActualAnalyticSources public

originalBishopSelectedNewtonFixedPoint :
  ∀ T →
  OriginalBishopNewtonActualAnalyticSources T →
  Complex.BishopComplex
originalBishopSelectedNewtonFixedPoint T source =
  let
    nz =
      Denominator.bishopNewtonDenominatorNonzeroFromOriginalSine
        T (selectedSinePositive source)
    steps =
      Disk.originalBishopAnalyticNewtonBuildsActualStepBounds
        T nz (selectedDiskCertificate source)
  in
  Limit.originalBishopSelectedNewtonLimit T nz steps

originalBishopSelectedNewtonFixedPointIsExpFixed :
  ∀ T →
  (source : OriginalBishopNewtonActualAnalyticSources T) →
  Complex._≈C_
    (Native.originalBishopExpOnSeries T
      (originalBishopSelectedNewtonFixedPoint T source))
    (originalBishopSelectedNewtonFixedPoint T source)
originalBishopSelectedNewtonFixedPointIsExpFixed T source =
  Continuity.originalBishopNewtonNativeExpFixedFromThreeScalarContinuities
    T
    (Denominator.bishopNewtonDenominatorNonzeroFromOriginalSine
      T (selectedSinePositive source))
    (selectedDiskCertificate source)
    (originalExpContinuousAlongNewton source)
    (originalCosContinuousAlongNewton source)
    (originalSinContinuousAlongNewton source)
