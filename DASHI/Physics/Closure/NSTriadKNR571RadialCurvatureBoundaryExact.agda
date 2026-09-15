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
-- the centered second-difference / Euclidean-radius curvature estimate.  This
-- owner names that leaf without manufacturing a bound from shell labels or
-- from the older incidence-only separation route abandoned after PR #890.
--
-- Expected analytic realization on a scoped annulus/nonzero-radius carrier:
--
--   ||x+y| - |x| - linear_x(y)| <= C |y|^2 / |x|
--
-- or an equivalent centered form sufficient for the preferred Taylor pair.
-- Existing finite centered/six-three compilers remain downstream consumers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact as GateA
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

-- The record above is deliberately the smallest A2 producer socket.  It does
-- not say that shell comparability, incidence geometry, or a finite family by
-- itself supplies the curvature constant.
r571A2RadialCurvatureIsolated : Bool
r571A2RadialCurvatureIsolated = true

r571A2PlusRemainderEliminatedByPreferredLinearization : Bool
r571A2PlusRemainderEliminatedByPreferredLinearization = true

r571A2UsesIncidenceOnlyCoercivity : Bool
r571A2UsesIncidenceOnlyCoercivity = false

r571A2UniformCurvatureEstimateClosed : Bool
r571A2UniformCurvatureEstimateClosed = false

r571A2InnerFibreGainClosed : Bool
r571A2InnerFibreGainClosed = false

r571A2ClosesR568 : Bool
r571A2ClosesR568 = false
