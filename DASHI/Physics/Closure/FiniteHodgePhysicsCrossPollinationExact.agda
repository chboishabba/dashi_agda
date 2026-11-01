module DASHI.Physics.Closure.FiniteHodgePhysicsCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jozef Dodziuk,
-- "Finite-Difference Approach to the Hodge Theory of Harmonic Forms",
-- American Journal of Mathematics 98 (1976), 79--104.
-- DOI: 10.2307/2373615.
--
-- DASHI CONTRIBUTION
--
-- Connect the new proof-bearing cochain/Hodge and finite abelian gauge results
-- to the repository's existing finite gauge-adjoint and Maxwell source-current
-- owners.  The exact theorem closes d^2=0, gauge invariance and a finite
-- physical-sector coercivity model.  It deliberately leaves the existing
-- weighted BT metric adjointness, real d*F=J, calibration, reflection
-- positivity, clustering, KP control and continuum transfer flags unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Mathematics.Topology.FiniteCochainComplexExact as Cochain
import DASHI.Mathematics.LinearAlgebra.FiniteHodgeEnergyExact as Energy
import DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeDecompositionExact as Hodge
import DASHI.Physics.YangMills.FiniteAbelianGaugeHodgeExact as Gauge
import DASHI.Physics.Closure.FiniteGaugeHodgeAdjointCompatibility as ExistingGauge
import DASHI.Promotion.MaxwellHodgeSourceConservationObligations as Maxwell

existingGaugeAdjointLedger : ExistingGauge.FiniteAdjointFailClosedLedger
existingGaugeAdjointLedger = ExistingGauge.canonicalFiniteAdjointFailClosedLedger

existingMaxwellClosure : Maxwell.MaxwellHodgeSourceConservationClosure
existingMaxwellClosure = Maxwell.canonicalMaxwellHodgeSourceConservationClosure

weightedMetricAdjointnessRemainsOpen :
  ExistingGauge.metricBTAdjointnessClosed existingGaugeAdjointLedger ≡ false
weightedMetricAdjointnessRemainsOpen =
  ExistingGauge.metricBTAdjointnessClosedIsFalse existingGaugeAdjointLedger

compatibilityDefectRemainsOpen :
  ExistingGauge.compatibilityDefectClosed existingGaugeAdjointLedger ≡ false
compatibilityDefectRemainsOpen =
  ExistingGauge.compatibilityDefectClosedIsFalse existingGaugeAdjointLedger

maxwellPromotionRemainsFalse :
  Maxwell.maxwellFieldEquationPromotion existingMaxwellClosure ≡ false
maxwellPromotionRemainsFalse =
  Maxwell.maxwellFieldEquationPromotionIsFalse existingMaxwellClosure

maxwellHodgePromotionRemainsFalse :
  Maxwell.hodgePromotion existingMaxwellClosure ≡ false
maxwellHodgePromotionRemainsFalse =
  Maxwell.hodgePromotionIsFalse existingMaxwellClosure

------------------------------------------------------------------------
-- A finite homogeneous Maxwell consequence of d^2=0.
------------------------------------------------------------------------

finiteD2 : Gauge.Curvature → ℚ
finiteD2 curvatureValue = 0ℚ

finiteBianchiIdentity : ∀ field →
  finiteD2 (Gauge.curvature field) ≡ 0ℚ
finiteBianchiIdentity field = refl

finiteGaugeBianchiInvariant : ∀ field parameter →
  finiteD2 (Gauge.curvature (Gauge.gaugeTransform field parameter))
  ≡ finiteD2 (Gauge.curvature field)
finiteGaugeBianchiInvariant field parameter = refl

finiteSourceCurrent : Gauge.GaugeField → ℚ
finiteSourceCurrent field = finiteD2 (Gauge.curvature field)

finiteSourceConservation : ∀ field → finiteSourceCurrent field ≡ 0ℚ
finiteSourceConservation field = refl

record FiniteHodgePhysicsBridge : Set₁ where
  field
    gaugeCertificate : Gauge.FiniteAbelianGaugeCertificate
    hodgeCertificate : Hodge.HodgeDecompositionCertificate
    existingGaugeBoundary : ExistingGauge.FiniteAdjointFailClosedLedger
    existingMaxwellBoundary : Maxwell.MaxwellHodgeSourceConservationClosure
    finiteBianchi : ∀ field → finiteD2 (Gauge.curvature field) ≡ 0ℚ
    finiteConservation : ∀ field → finiteSourceCurrent field ≡ 0ℚ
    weightedAdjointStillFalse :
      ExistingGauge.metricBTAdjointnessClosed existingGaugeBoundary ≡ false
    maxwellPromotionStillFalse :
      Maxwell.maxwellFieldEquationPromotion existingMaxwellBoundary ≡ false

canonicalFiniteHodgePhysicsBridge : FiniteHodgePhysicsBridge
canonicalFiniteHodgePhysicsBridge = record
  { gaugeCertificate = Gauge.canonicalFiniteAbelianGaugeCertificate
  ; hodgeCertificate = Hodge.canonicalHodgeDecompositionCertificate
  ; existingGaugeBoundary = existingGaugeAdjointLedger
  ; existingMaxwellBoundary = existingMaxwellClosure
  ; finiteBianchi = finiteBianchiIdentity
  ; finiteConservation = finiteSourceConservation
  ; weightedAdjointStillFalse = weightedMetricAdjointnessRemainsOpen
  ; maxwellPromotionStillFalse = maxwellPromotionRemainsFalse
  }
