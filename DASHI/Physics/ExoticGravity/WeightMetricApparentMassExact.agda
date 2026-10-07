module DASHI.Physics.ExoticGravity.WeightMetricApparentMassExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- WEIGHT / APPARENT MASS / METRIC ARE DISTINCT OBSERVABLE COORDINATES
--
-- A scale measures a support-force observable.  Interpreting that reading as
-- an apparent mass requires a reference acceleration/calibration.  Neither the
-- support-force reading nor the inferred apparent mass is definitionally the
-- inertial mass, passive gravitational response, or spacetime metric.
------------------------------------------------------------------------

data WeightChangeCause : Set where
  metricChanged : WeightChangeCause
  worldlineAccelerationChanged : WeightChangeCause
  supportInteractionChanged : WeightChangeCause
  passiveGravitationalResponseChanged : WeightChangeCause
  inertialResponseChanged : WeightChangeCause
  ordinaryEMForceChanged : WeightChangeCause
  thermalBuoyancyMechanicalChanged : WeightChangeCause

record WeightExperiment : Set₁ where
  constructor weight-experiment
  field
    Metric : Set
    Worldline : Set
    SupportState : Set
    SupportForce : Set
    ReferenceGravityCalibration : Set
    ApparentWeight : Set
    ApparentMass : Set
    InertialMass : Set
    PassiveGravitationalResponse : Set

    supportForceObservable :
      Metric → Worldline → SupportState → SupportForce

    inferApparentWeight :
      SupportForce → ApparentWeight

    inferApparentMass :
      ReferenceGravityCalibration → ApparentWeight → ApparentMass

    metric : Metric
    worldline : Worldline
    supportState : SupportState
    referenceGravityCalibration : ReferenceGravityCalibration
    inertialMass : InertialMass
    passiveGravitationalResponse : PassiveGravitationalResponse

open WeightExperiment public

apparentWeightReadout :
  (experiment : WeightExperiment) →
  ApparentWeight experiment
apparentWeightReadout experiment =
  inferApparentWeight experiment
    (supportForceObservable experiment
      (metric experiment)
      (worldline experiment)
      (supportState experiment))

apparentMassReadout :
  (experiment : WeightExperiment) →
  ApparentMass experiment
apparentMassReadout experiment =
  inferApparentMass experiment
    (referenceGravityCalibration experiment)
    (apparentWeightReadout experiment)

------------------------------------------------------------------------
-- A metric change can alter a weight reading only through a specified
-- worldline/support model.  The reverse implication is invalid because many
-- non-metric coordinates can alter the same support-force observable.
------------------------------------------------------------------------

record MetricConditionedWeightPrediction
    (experiment : WeightExperiment) : Set₁ where
  constructor metric-conditioned-weight-prediction
  field
    baselineMetric : Metric experiment
    changedMetric : Metric experiment
    fixedWorldline : Worldline experiment
    fixedSupportState : SupportState experiment

    baselineSupportForce : SupportForce experiment
    changedSupportForce : SupportForce experiment

    baselineForceIsPredicted :
      baselineSupportForce
      ≡ supportForceObservable experiment
          baselineMetric fixedWorldline fixedSupportState

    changedForceIsPredicted :
      changedSupportForce
      ≡ supportForceObservable experiment
          changedMetric fixedWorldline fixedSupportState

open MetricConditionedWeightPrediction public

------------------------------------------------------------------------
-- Empty automatic-identification propositions.
------------------------------------------------------------------------

data WeightChangeForcesMetricChange : Set where
data ApparentMassEqualsInertialMass : Set where
data ApparentMassEqualsPassiveGravitationalResponse : Set where

weightChangeDoesNotForceMetricChange : WeightChangeForcesMetricChange → ⊥
weightChangeDoesNotForceMetricChange ()

apparentMassIsNotDefinitionallyInertialMass :
  ApparentMassEqualsInertialMass → ⊥
apparentMassIsNotDefinitionallyInertialMass ()

apparentMassIsNotDefinitionallyPassiveGravitationalResponse :
  ApparentMassEqualsPassiveGravitationalResponse → ⊥
apparentMassIsNotDefinitionallyPassiveGravitationalResponse ()

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record WeightMetricBoundary : Set where
  constructor weight-metric-boundary
  field
    weightChangeImpliesMetricChange : Bool
    weightChangeImpliesMetricChangeIsFalse :
      weightChangeImpliesMetricChange ≡ false

    metricChangeCanAlterWeightGivenSupportModel : Bool
    metricChangeCanAlterWeightGivenSupportModelIsTrue :
      metricChangeCanAlterWeightGivenSupportModel ≡ true

    apparentMassIsInertialMassByDefinition : Bool
    apparentMassIsInertialMassByDefinitionIsFalse :
      apparentMassIsInertialMassByDefinition ≡ false

    apparentMassIsPassiveGravitationalResponseByDefinition : Bool
    apparentMassIsPassiveGravitationalResponseByDefinitionIsFalse :
      apparentMassIsPassiveGravitationalResponseByDefinition ≡ false

    supportForceClosureRequiredBeforeGravityPromotion : Bool
    supportForceClosureRequiredBeforeGravityPromotionIsTrue :
      supportForceClosureRequiredBeforeGravityPromotion ≡ true

    freeFallOrMetricProbeRequiredForMetricClaim : Bool
    freeFallOrMetricProbeRequiredForMetricClaimIsTrue :
      freeFallOrMetricProbeRequiredForMetricClaim ≡ true

canonicalWeightMetricBoundary : WeightMetricBoundary
canonicalWeightMetricBoundary =
  weight-metric-boundary
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
