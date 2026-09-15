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
-- The current centered-shift tranche source-writes on the literal rational
-- Fourier carrier:
--
--   (k+y) + (k-y) = 2k,
--   |2k|^2 = 4|k|^2,
--   Plucker(k+y,k-y) = 4 Plucker(k,y),
--   modeNorm(2k) = 2 modeNorm(k),
--
-- together with the aligned complement
--
--   (r_p-r_q)^2 + r_p r_q ||P-Q||^2 = |p-q|^2,
--   r_p r_q ||P-Q||^2 <= 4 |y|^2.
--
-- The centered product bridge then proves exactly
--
--   (r_p+r_q-2r_k)(r_p+r_q+2r_k)
--     = r_p r_q ||P-Q||^2
--     <= 4 |y|^2,
--
-- and the division-free order compiler yields
--
--   r_k (r_p+r_q-2r_k) <= 4 |y|^2.
--
-- Thus the previously named ordered radial-denominator leaf is paid without
-- division or an annular lower bound.  The remaining A2 seam is only the
-- same-object transport of this literal curvature payment into the exact
-- Gate-A `minusRemainderCurvatureBound` sample interface.
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
import DASHI.Physics.Closure.NSTriadKNR571CenteredAlignedComplementExact as Aligned
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialDenominatorOrderExact as Denominator
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialProductBridgeExact as ProductBridge
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

r571A2LiteralAlignedComplementIdentityClosed : Bool
r571A2LiteralAlignedComplementIdentityClosed =
  Aligned.r571A2LiteralAlignedComplementIdentityClosed

r571A2AlignedAngularSecondMomentPaymentClosed : Bool
r571A2AlignedAngularSecondMomentPaymentClosed =
  Aligned.r571A2CenteredAlignedAngularSecondMomentPaymentClosed

r571A2DivisionFreeDenominatorCompilerClosed : Bool
r571A2DivisionFreeDenominatorCompilerClosed =
  Denominator.r571A2DivisionFreeDenominatorCompilerClosed

r571A2LiteralCenteredProductBridgeClosed : Bool
r571A2LiteralCenteredProductBridgeClosed =
  ProductBridge.r571A2LiteralCenteredProductBridgeClosed

r571A2OrderedRadialDenominatorPaymentClosed : Bool
r571A2OrderedRadialDenominatorPaymentClosed =
  ProductBridge.r571A2DivisionFreeRadialCurvaturePaymentClosed

r571A2UsesIncidenceOnlyCoercivity : Bool
r571A2UsesIncidenceOnlyCoercivity = false

-- The local centered Euclidean-radius curvature is now paid.  This flag stays
-- false until the exact sign/absolute-value/stepMagnitude transport into
-- R571PreferredRadialCurvatureSample is source-written.
r571A2UniformCurvatureEstimateClosed : Bool
r571A2UniformCurvatureEstimateClosed = false

r571A2InnerFibreGainClosed : Bool
r571A2InnerFibreGainClosed = false

r571A2ClosesR568 : Bool
r571A2ClosesR568 = false
