module DASHI.Control.McCaslandFailureSetPlacementCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Source-shaped algorithm owner for McCasland fault-tolerant sensor/actuator
-- placement.  The source uses controllability/observability Gramian norms as
-- placement performance measures under failures and reconfiguration.

data PlacementKind : Set where sensorPlacement actuatorPlacement : PlacementKind

data FailureMode : Set where noFailure singleSensorFailure singleActuatorFailure multipleFailure : FailureMode

record PlacementCandidate : Set where
  constructor placement-candidate
  field
    kind : PlacementKind
    placementLabel : String
    gramianMetric : String
    coordinateScaling : String

open PlacementCandidate public

record FailureSetEvaluation : Set where
  constructor failure-set-evaluation
  field
    candidate : PlacementCandidate
    failure : FailureMode
    residualPlacement : String
    residualGramianMetric : String
    reconfigurationPolicy : String
    sourceReference : String

open FailureSetEvaluation public

record FaultTolerantPlacementReceipt : Set where
  constructor fault-tolerant-placement-receipt
  field
    nominalEvaluation : FailureSetEvaluation
    failedEvaluation : FailureSetEvaluation
    failureFamilyExplicit : Bool
    failureFamilyExplicitIsTrue : failureFamilyExplicit ≡ true
    residualControllabilityOrObservabilityChecked : Bool
    residualControllabilityOrObservabilityCheckedIsTrue :
      residualControllabilityOrObservabilityChecked ≡ true
    reconfigurationExplicit : Bool
    reconfigurationExplicitIsTrue : reconfigurationExplicit ≡ true

open FaultTolerantPlacementReceipt public

record McCaslandPlacementBoundary : Set where
  constructor mccasland-placement-boundary
  field
    nominalBestImpliesFailureBest : Bool
    nominalBestImpliesFailureBestIsFalse : nominalBestImpliesFailureBest ≡ false
    highGramianNormImpliesAllFailureSetsCovered : Bool
    highGramianNormImpliesAllFailureSetsCoveredIsFalse : highGramianNormImpliesAllFailureSetsCovered ≡ false
    coordinateRescalingLeavesGramianNormNumericallyInvariant : Bool
    coordinateRescalingLeavesGramianNormNumericallyInvariantIsFalse :
      coordinateRescalingLeavesGramianNormNumericallyInvariant ≡ false
    faultToleranceNeedsExplicitFailureFamily : Bool
    faultToleranceNeedsExplicitFailureFamilyIsTrue :
      faultToleranceNeedsExplicitFailureFamily ≡ true

canonicalMcCaslandPlacementBoundary : McCaslandPlacementBoundary
canonicalMcCaslandPlacementBoundary =
  mccasland-placement-boundary false refl false refl false refl true refl
