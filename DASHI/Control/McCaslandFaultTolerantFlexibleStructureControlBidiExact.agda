module DASHI.Control.McCaslandFaultTolerantFlexibleStructureControlBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- W. Neil McCasland
-- Sensor and Actuator Selection for Fault-Tolerant Control of Flexible Structures
-- MIT/AFIT PhD thesis; Hertz Thesis Prize 1989; NASA/NTIS AD-A217384.
-- Related paper: 1989 American Control Conference, pp. 1111-1116.
--
-- Source-backed mathematical content:
-- * flexible structural dynamics require sensor/actuator placement;
-- * placement quality is measured with controllability/observability Gramian norms;
-- * long-duration spacecraft motivate explicit failure coverage;
-- * redundancy plus a reconfiguration strategy is required;
-- * examples include a simply supported beam and a large finite-element model.
------------------------------------------------------------------------

data PlacementObject : Set where
  sensor actuator sensorActuatorPair : PlacementObject


data FailureMode : Set where
  sensorFailure actuatorFailure multipleComponentFailure : FailureMode


data ControlProperty : Set where
  controllability observability faultCoverage reconfigurability : ControlProperty

record FlexibleStructureControlModel : Set₁ where
  constructor flexible-structure-control-model
  field
    State Input Output : Set
    dynamicsReference : String
    candidateSensors : List String
    candidateActuators : List String

open FlexibleStructureControlModel public

record GramianPerformanceMeasure : Set where
  constructor gramian-performance-measure
  field
    property : ControlProperty
    normDescription : String
    stateScalingRule : String
    sourceReference : String

open GramianPerformanceMeasure public

controllabilityGramianMeasure : GramianPerformanceMeasure
controllabilityGramianMeasure = gramian-performance-measure
  controllability
  "norm of controllability Gramian used as placement-performance measure"
  "state-space scaling based on selected throughput path"
  "McCasland 1989 ACC / PhD thesis"

observabilityGramianMeasure : GramianPerformanceMeasure
observabilityGramianMeasure = gramian-performance-measure
  observability
  "norm of observability Gramian used as placement-performance measure"
  "state-space scaling based on selected throughput path"
  "McCasland 1989 ACC / PhD thesis"

record FailureCoverageDesign : Set where
  constructor failure-coverage-design
  field
    nominalPlacement : String
    protectedFailureSet : List FailureMode
    redundantHardware : Bool
    redundantHardwareIsTrue : redundantHardware ≡ true
    reconfigurationStrategy : String
    sourceReference : String

open FailureCoverageDesign public

record McCaslandControlBoundary : Set where
  constructor mccasland-control-boundary
  field
    maximumNominalGramianAutomaticallyMaximisesFaultTolerance : Bool
    maximumNominalGramianAutomaticallyMaximisesFaultToleranceIsFalse :
      maximumNominalGramianAutomaticallyMaximisesFaultTolerance ≡ false

    redundancyWithoutReconfigurationGuaranteesRecovery : Bool
    redundancyWithoutReconfigurationGuaranteesRecoveryIsFalse :
      redundancyWithoutReconfigurationGuaranteesRecovery ≡ false

    controllabilityImpliesObservability : Bool
    controllabilityImpliesObservabilityIsFalse :
      controllabilityImpliesObservability ≡ false

    observabilityImpliesControllability : Bool
    observabilityImpliesControllabilityIsFalse :
      observabilityImpliesControllability ≡ false

    failureTolerantPlacementRequiresExplicitFailureSet : Bool
    failureTolerantPlacementRequiresExplicitFailureSetIsTrue :
      failureTolerantPlacementRequiresExplicitFailureSet ≡ true

canonicalMcCaslandControlBoundary : McCaslandControlBoundary
canonicalMcCaslandControlBoundary =
  mccasland-control-boundary false refl false refl false refl false refl true refl

record PlacementBidiObligation : Set where
  constructor placement-bidi-obligation
  field
    desiredProperty : ControlProperty
    candidatePlacement : String
    requiredSystemModel : String
    requiredGramianReceipt : String
    requiredFailureCoverage : String
    requiredReconfigurationReceipt : String
    cannotPromote : String

open PlacementBidiObligation public

faultTolerantSensorPlacementReverse : PlacementBidiObligation
faultTolerantSensorPlacementReverse = placement-bidi-obligation
  observability
  "proposed sensor locations on flexible structure"
  "scaled structural state-space / finite-element dynamics"
  "observability-Gramian performance under nominal and failed configurations"
  "enumerated protected sensor/actuator failure set"
  "post-failure estimator/controller reconfiguration strategy"
  "fault tolerance from nominal placement quality alone"
