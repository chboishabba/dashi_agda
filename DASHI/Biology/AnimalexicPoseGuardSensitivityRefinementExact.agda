module DASHI.Biology.AnimalexicPoseGuardSensitivityRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ANIMALEXIC POSE/WELD -> GUARD SENSITIVITY + QUALITY-TARGETED REFINEMENT
--
-- The runtime now has a controlled consumer experiment over the exact existing
-- voxel guard.  Geometry error coordinates are injected one at a time and the
-- resulting guard state is compared with the known/oracle transport surface.
--
-- This is the Animalexic analogue of the dashiRTX light-transport discipline:
-- transport -> consumer residual/frontier -> targeted refinement.  It is not a
-- weighted scalar optimizer and it does not identify lower error with truth.
------------------------------------------------------------------------

record PoseGuardSensitivityImplementationReceipt : Set where
  constructor pose-guard-sensitivity-implementation-receipt
  field
    sensitivityRuntimeReference : String
    controlledExperimentReference : String
    existingVoxelGuardReused : Bool
    cameraOriginPerturbationCoordinate : Bool
    orientationPerturbationCoordinate : Bool
    metricScalePerturbationCoordinate : Bool
    observationResidualPerturbationCoordinate : Bool
    stateAgreementMeasured : Bool
    ascendedIoUMeasured : Bool
    maximumScoreResidualMeasured : Bool
    signedTernaryFrontierMeasured : Bool
    weightedScalarObjectiveIntroduced : Bool
    paretoRefinementFrontierImplemented : Bool

open PoseGuardSensitivityImplementationReceipt public

currentPoseGuardSensitivityImplementationReceipt : PoseGuardSensitivityImplementationReceipt
currentPoseGuardSensitivityImplementationReceipt =
  pose-guard-sensitivity-implementation-receipt
    "chboishabba/animalexic/scripts/pose_guard_sensitivity.py"
    "chboishabba/animalexic/scripts/pose_guard_sensitivity_experiment.py"
    true true true true true true true true true false true

------------------------------------------------------------------------
-- Controlled exact-content mirror receipt.
--
-- The repository cannot currently be cloned/downloaded through the execution
-- environment DNS path, so branch Python files were mirrored from the connector
-- content and executed locally.  This is stronger than an unevaluated source
-- claim but remains separate from an exact repository-checkout execution.
------------------------------------------------------------------------

record ControlledSensitivityExecutionReceipt : Set where
  constructor controlled-sensitivity-execution-receipt
  field
    schemaReference : String
    exactContentMirrorProbePaid : Bool
    focusedTestsPassed : String
    repositoryCheckoutExecutionPaid : Bool
    issue20ArchiveExecutionPaid : Bool
    realPhoneExecutionPaid : Bool

open ControlledSensitivityExecutionReceipt public

currentControlledSensitivityExecutionReceipt : ControlledSensitivityExecutionReceipt
currentControlledSensitivityExecutionReceipt =
  controlled-sensitivity-execution-receipt
    "animalexic_pose_guard_sensitivity_v1"
    true
    "9/9 focused sensitivity/refinement tests"
    false
    false
    false

------------------------------------------------------------------------
-- Controlled portfolio result.  These are synthetic-consumer measurements,
-- not field tolerances and not universal camera-pose error bounds.
------------------------------------------------------------------------

record ControlledSensitivityRow : Set where
  constructor controlled-sensitivity-row
  field
    name : String
    stateAgreement : String
    ascendedIoU : String
    maxAbsScoreResidual : String
    stateChangeCount : String
    frontierNonzeroCount : String
    withinPolicy : Bool

open ControlledSensitivityRow public

oracleRow : ControlledSensitivityRow
oracleRow = controlled-sensitivity-row
  "oracle" "1.0" "1.0" "0.0" "0" "0" true

origin25cmRow : ControlledSensitivityRow
origin25cmRow = controlled-sensitivity-row
  "origin_25cm" "0.966269841" "0.392857143" "0.202484906" "51" "51" false

yaw10degRow : ControlledSensitivityRow
yaw10degRow = controlled-sensitivity-row
  "yaw_10deg" "0.959656085" "0.314606742" "0.206031084" "61" "61" false

scalePlus10pctRow : ControlledSensitivityRow
scalePlus10pctRow = controlled-sensitivity-row
  "scale_plus_10pct" "0.993386243" "0.852941176" "0.164602503" "10" "10" false

residualPlus5Row : ControlledSensitivityRow
residualPlus5Row = controlled-sensitivity-row
  "residual_plus_5" "0.99537037" "0.887096774" "0.091839246" "7" "7" false

record ControlledParetoReceipt : Set where
  constructor controlled-pareto-receipt
  field
    weightedScalarizationUsed : Bool
    paretoMaximalDefectReference : String

open ControlledParetoReceipt public

currentControlledParetoReceipt : ControlledParetoReceipt
currentControlledParetoReceipt = controlled-pareto-receipt false "yaw_10deg"

------------------------------------------------------------------------
-- Quality-targeted refinement can terminate with paid consumer adequacy,
-- max-steps debt, or a quantization plateau.  A smaller producer coordinate is
-- not enough to claim closure if the consumer surface stops improving.
------------------------------------------------------------------------

record QuantizedYawRefinementReceipt : Set where
  constructor quantized-yaw-refinement-receipt
  field
    initialYawDegrees : String
    finalTestedYawDegrees : String
    refinementStepsExecuted : String
    finalStateAgreement : String
    finalAscendedIoU : String
    finalMaxAbsScoreResidual : String
    finalStateChangeCount : String
    consumerPolicyPaid : Bool
    termination : String

open QuantizedYawRefinementReceipt public

currentQuantizedYawRefinementReceipt : QuantizedYawRefinementReceipt
currentQuantizedYawRefinementReceipt =
  quantized-yaw-refinement-receipt
    "10.0"
    "0.15625"
    "7"
    "0.998015873015873"
    "0.9523809523809523"
    "0.1798684000968933"
    "3"
    false
    "consumer_plateau"

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data SmallerPoseErrorImpliesConsumerClosurePermission : Set where

data ConsumerPlateauImpliesProducerTruthPermission : Set where

data SyntheticToleranceImpliesFieldTolerancePermission : Set where

data ParetoMaximalDefectImpliesUniqueCausalDefectPermission : Set where

smallerPoseErrorDoesNotAutoPayConsumerClosure :
  SmallerPoseErrorImpliesConsumerClosurePermission → ⊥
smallerPoseErrorDoesNotAutoPayConsumerClosure ()

consumerPlateauDoesNotAutoPayProducerTruth :
  ConsumerPlateauImpliesProducerTruthPermission → ⊥
consumerPlateauDoesNotAutoPayProducerTruth ()

syntheticToleranceDoesNotAutoPayFieldTolerance :
  SyntheticToleranceImpliesFieldTolerancePermission → ⊥
syntheticToleranceDoesNotAutoPayFieldTolerance ()

paretoMaximalDefectDoesNotProveUniqueCause :
  ParetoMaximalDefectImpliesUniqueCausalDefectPermission → ⊥
paretoMaximalDefectDoesNotProveUniqueCause ()

------------------------------------------------------------------------
-- Live frontier.
------------------------------------------------------------------------

record PoseGuardSensitivityNextResidual : Set where
  constructor pose-guard-sensitivity-next-residual
  field
    executeExactRepositoryCheckout : Bool
    replaceSyntheticOracleWithIssue20KnownPose : Bool
    feedImageRecoveredPoseThroughGuard : Bool
    feedRobustWorldWeldThroughGuard : Bool
    measureOriginOrientationScaleResidualFibreInteractions : Bool
    validateSurfelConsumerSurface : Bool
    validateRealMultiphoneCarrier : Bool

open PoseGuardSensitivityNextResidual public

currentPoseGuardSensitivityNextResidual : PoseGuardSensitivityNextResidual
currentPoseGuardSensitivityNextResidual =
  pose-guard-sensitivity-next-residual true true true true true true true
