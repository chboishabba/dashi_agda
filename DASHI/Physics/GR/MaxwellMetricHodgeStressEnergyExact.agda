module DASHI.Physics.GR.MaxwellMetricHodgeStressEnergyExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Laws.GaugeInteractionLaws as Gauge
import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange

------------------------------------------------------------------------
-- MAXWELL METRIC/HODGE -> STRESS-ENERGY SAME-OBJECT SEAM
--
-- The repo already has a MaxwellFieldLaw with a literal metric-dependent
-- Hodge star.  Therefore the controlled EM-GW programme must consume that
-- object rather than invent a second Hodge carrier.  What remains physical is
-- the Hilbert/metric first-variation identification of the stress tensor.
------------------------------------------------------------------------

record MaxwellMetricHodgeState (maxwell : Gauge.MaxwellFieldLaw) : Set₁ where
  constructor maxwell-metric-hodge-state
  field
    metric : Gauge.MaxwellFieldLaw.Metric maxwell
    orientation : Gauge.MaxwellFieldLaw.Orientation maxwell
    fieldStrength : Gauge.MaxwellFieldLaw.TwoForm maxwell

    fieldStrengthIsFromExistingPotential :
      fieldStrength
      ≡ Gauge.MaxwellFieldLaw.fieldStrength maxwell
          (Gauge.MaxwellFieldLaw.potential maxwell)

    hodgeDual : Gauge.MaxwellFieldLaw.TwoForm maxwell
    hodgeDualIsExistingHodgeStar :
      hodgeDual
      ≡ Gauge.MaxwellFieldLaw.hodgeStar maxwell metric orientation fieldStrength

open MaxwellMetricHodgeState public

canonicalMaxwellMetricHodgeState :
  (maxwell : Gauge.MaxwellFieldLaw) →
  (metric : Gauge.MaxwellFieldLaw.Metric maxwell) →
  (orientation : Gauge.MaxwellFieldLaw.Orientation maxwell) →
  MaxwellMetricHodgeState maxwell
canonicalMaxwellMetricHodgeState maxwell metric orientation = record
  { metric = metric
  ; orientation = orientation
  ; fieldStrength =
      Gauge.MaxwellFieldLaw.fieldStrength maxwell
        (Gauge.MaxwellFieldLaw.potential maxwell)
  ; fieldStrengthIsFromExistingPotential = refl
  ; hodgeDual =
      Gauge.MaxwellFieldLaw.hodgeStar maxwell metric orientation
        (Gauge.MaxwellFieldLaw.fieldStrength maxwell
          (Gauge.MaxwellFieldLaw.potential maxwell))
  ; hodgeDualIsExistingHodgeStar = refl
  }

------------------------------------------------------------------------
-- Hilbert stress-energy interface.
--
-- No extra Maxwell or Hodge authority is requested here: metric, orientation,
-- F and *F all come from the existing MaxwellFieldLaw.  The remaining theorem
-- is exactly that variation of the same Maxwell action with respect to the
-- same metric is represented by the supplied EM stress-energy object.
------------------------------------------------------------------------

record MaxwellHilbertStressEnergy
    (maxwell : Gauge.MaxwellFieldLaw)
    (state : MaxwellMetricHodgeState maxwell) : Set₁ where
  constructor maxwell-hilbert-stress-energy
  field
    MetricTangent : Set
    ActionValue : Set
    StressEnergy : Set

    maxwellAction :
      Gauge.MaxwellFieldLaw.Metric maxwell →
      Gauge.MaxwellFieldLaw.Orientation maxwell →
      Gauge.MaxwellFieldLaw.TwoForm maxwell →
      Gauge.MaxwellFieldLaw.TwoForm maxwell →
      ActionValue

    metricFirstVariation : MetricTangent → ActionValue
    stressEnergy : StressEnergy

    ActionUsesSameFAndHodgeDual : Set
    actionUsesSameFAndHodgeDual : ActionUsesSameFAndHodgeDual

    HilbertStressVariationReceipt : Set
    hilbertStressVariationReceipt : HilbertStressVariationReceipt

    StressConservationReceipt : Set
    stressConservationReceipt : StressConservationReceipt

open MaxwellHilbertStressEnergy public

record MaxwellHilbertExchangeWeld
    (maxwell : Gauge.MaxwellFieldLaw)
    (state : MaxwellMetricHodgeState maxwell)
    (stress : MaxwellHilbertStressEnergy maxwell state) : Set₁ where
  constructor maxwell-hilbert-exchange-weld
  field
    interaction : Exchange.EMGWInteractionCarrier

    MetricPerturbationToMetricTangent : Set
    metricPerturbationToMetricTangent : MetricPerturbationToMetricTangent

    SameEMStressEnergyReceipt : Set
    sameEMStressEnergyReceipt : SameEMStressEnergyReceipt

    SameLinearisedInteractionReceipt : Set
    sameLinearisedInteractionReceipt : SameLinearisedInteractionReceipt

open MaxwellHilbertExchangeWeld public

------------------------------------------------------------------------
-- Scope accounting.
------------------------------------------------------------------------

record MaxwellMetricHodgeStressBoundary : Set where
  constructor maxwell-metric-hodge-stress-boundary
  field
    existingMaxwellFieldStrengthReused : Bool
    existingMetricDependentHodgeStarReused : Bool
    separateHodgeAuthorityNeededForThisInterface : Bool
    hilbertMetricVariationStillRequiresPhysicalReceipt : Bool
    stressConservationStillRequiresPhysicalReceipt : Bool
    exchangeSameObjectWeldStillRequiresReceipt : Bool

canonicalMaxwellMetricHodgeStressBoundary : MaxwellMetricHodgeStressBoundary
canonicalMaxwellMetricHodgeStressBoundary =
  maxwell-metric-hodge-stress-boundary
    true true false true true true
