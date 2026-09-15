module DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureBoundaryExact where

------------------------------------------------------------------------
-- R571 GATE-A / A2 RADIAL CURVATURE BOUNDARY
--
-- After choosing the +y radial increment itself as the Taylor linear model,
-- the + remainder is exactly zero.  The radial Taylor problem therefore
-- collapses to ONE quantitative remainder:
--
--   | m(k-y) - m(k) + (m(k+y)-m(k)) |
--      <= |y|^2 A2.
--
-- For the homochiral R571 multiplier m_sigma(k) = sigma |k| this is precisely
-- the centered second-difference / Euclidean-radius curvature estimate.
--
-- The square-gap owner pays the exact denominator-cleared algebra.  The
-- centered-shift owners additionally prove on the literal rational Fourier
-- carrier
--
--   (k+y) + (k-y) = 2k,
--   |2k|^2 = 4|k|^2,
--   Plucker(k+y,k-y) = 4 Plucker(k,y),
--   modeNorm(2k) = 2 modeNorm(k).
--
-- Radius doubling is obtained from R455 square calibration + nonnegative root
-- separation, not a square-root axiom.  The remaining A2 payment is now the
-- ordered/annular denominator control and final aligned angular/square-gap
-- second-moment bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact as GateA
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureSquareGapExact as SquareGap
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as CenteredShift
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftRadiusDoublingExact as RadiusDouble
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor

record R571PreferredRadialCurvatureSample : Set₁ where
  field
    sign : R311.HelicitySign
    scalars : Helical.HelicalModeScalars Weld.F
    center plus minus : Z3.FourierMode
    stepMagnitude transportCurvature : ℚ
    stepMagnitudeNonnegative : 0ℚ ≤ stepMagnitude
    transportCurvatureNonnegative : 0ℚ ≤ transportCurvature

    minusRemainderCurvatureBound :
      ∣ Taylor.minusRemainder
          (GateA.preferredRadialTaylorPair sign scalars center plus minus) ∣
      ≤ stepMagnitude * stepMagnitude * transportCurvature

open R571PreferredRadialCurvatureSample public

preferredPlusRemainderIsExactlyZero :
  (sample : R571PreferredRadialCurvatureSample) →
  Taylor.plusRemainder
    (GateA.preferredRadialTaylorPair
      (sign sample) (scalars sample)
      (center sample) (plus sample) (minus sample))
  ≡ 0ℚ
preferredPlusRemainderIsExactlyZero sample =
  GateA.preferredPlusRemainderZero
    (sign sample) (scalars sample)
    (center sample) (plus sample) (minus sample)

r571A2RadialCurvatureIsolated : Bool
r571A2RadialCurvatureIsolated = true

r571A2PlusRemainderEliminatedByPreferredLinearization : Bool
r571A2PlusRemainderEliminatedByPreferredLinearization = true

r571A2SquareGapNumeratorReductionClosed : Bool
r571A2SquareGapNumeratorReductionClosed =
  SquareGap.r571A2CenteredRadiusDefectSquareGapRationalized

r571A2CenteredShiftModeGeometryClosed : Bool
r571A2CenteredShiftModeGeometryClosed =
  CenteredShift.r571A2CenteredShiftModeSumClosed

r571A2CenteredShiftSquaredOutputScalingClosed : Bool
r571A2CenteredShiftSquaredOutputScalingClosed =
  CenteredShift.r571A2CenteredShiftSquaredOutputScalingClosed

r571A2CenteredShiftPluckerScalingClosed : Bool
r571A2CenteredShiftPluckerScalingClosed =
  CenteredShift.r571A2CenteredShiftPluckerScalingClosed

r571A2CenteredShiftScalarRadiusDoublingClosed : Bool
r571A2CenteredShiftScalarRadiusDoublingClosed =
  RadiusDouble.r571A2CenteredShiftScalarRadiusDoublingClosed

r571A2OrderedRadialDenominatorPaymentClosed : Bool
r571A2OrderedRadialDenominatorPaymentClosed =
  SquareGap.r571A2OrderedRadialDenominatorPaymentClosed

r571A2UsesIncidenceOnlyCoercivity : Bool
r571A2UsesIncidenceOnlyCoercivity = false

r571A2UniformCurvatureEstimateClosed : Bool
r571A2UniformCurvatureEstimateClosed = false

r571A2InnerFibreGainClosed : Bool
r571A2InnerFibreGainClosed = false

r571A2ClosesR568 : Bool
r571A2ClosesR568 = false
