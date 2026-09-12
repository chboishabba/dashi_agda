module DASHI.Biology.AnimalexicHandheldMultiCameraPoseFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedModelFibreExact as Consumer

------------------------------------------------------------------------
-- ANIMALEXIC HANDHELD MULTI-CAMERA POSE FIBRE
--
-- Camera pose is not a one-off calibration constant in Regime B.  It is a
-- time-indexed geometry candidate assembled from visual-static-scene evidence,
-- IMU priors, cross-camera correspondences, clock alignment and metric-scale
-- receipts.  This module is a typed boundary over runtime producers; it does
-- not claim to implement VIO, SfM, bundle adjustment or SLAM in Agda.
------------------------------------------------------------------------

record PoseEvidenceReceipt : Set where
  constructor pose-evidence-receipt
  field
    cameraReference : String
    timeReference : String
    visualStaticSceneEvidence : Bool
    imuPriorEvidence : Bool
    crossCameraCorrespondenceEvidence : Bool
    metricScalePaid : Bool
    clockAlignmentPaid : Bool
    rollingShutterPaid : Bool
    provenanceReference : String

open PoseEvidenceReceipt public

record CameraPoseFibre : Set where
  constructor camera-pose-fibre
  field
    localTrajectoryReference : String
    sharedWorldTransformReference : String
    clockOffsetReference : String
    rollingShutterReference : String
    uncertaintyReference : String
    outputIsCandidate : Bool

open CameraPoseFibre public

------------------------------------------------------------------------
-- Dynamic target evidence and camera-motion evidence must remain separated.
-- A moving dog can inform the body/spatial fibre while being inadmissible for
-- estimating the camera trajectory that will later locate that dog.
------------------------------------------------------------------------

data DynamicTargetEvidenceImpliesCameraPosePermission : Set where

dynamicTargetEvidenceDoesNotAutoDetermineCameraPose :
  DynamicTargetEvidenceImpliesCameraPosePermission → ⊥
dynamicTargetEvidenceDoesNotAutoDetermineCameraPose ()

------------------------------------------------------------------------
-- IMU is a prior/observer.  It does not, by itself, provide camera-pose truth.
------------------------------------------------------------------------

data IMUPriorImpliesAuthoritativeCameraPosePermission : Set where

imuPriorDoesNotAutoPromoteToAuthoritativePose :
  IMUPriorImpliesAuthoritativeCameraPosePermission → ⊥
imuPriorDoesNotAutoPromoteToAuthoritativePose ()

------------------------------------------------------------------------
-- Monocular/cross-view geometry can determine orientation and translation
-- direction without paying metric translation scale.  Keep this debt typed.
------------------------------------------------------------------------

data RelativePoseImpliesMetricScalePermission : Set where

relativePoseDoesNotAutoPayMetricScale :
  RelativePoseImpliesMetricScalePermission → ⊥
relativePoseDoesNotAutoPayMetricScale ()

------------------------------------------------------------------------
-- Shared sky / effectively-infinite landmarks may strongly constrain camera
-- orientation but do not automatically determine terrestrial translation.
------------------------------------------------------------------------

data SharedSkyImpliesTerrestrialTranslationPermission : Set where

sharedSkyDoesNotAutoDetermineTranslation :
  SharedSkyImpliesTerrestrialTranslationPermission → ⊥
sharedSkyDoesNotAutoDetermineTranslation ()

------------------------------------------------------------------------
-- Pose adequacy is indexed by the downstream consumer.  A pose estimate can
-- be adequate for coarse voxel-ray intersection yet inadequate for fine surfel
-- fusion or body-pose reconstruction.
------------------------------------------------------------------------

record PoseConsumerAdequacy : Set where
  constructor pose-consumer-adequacy
  field
    consumerReference : String
    confidenceBoundPaid : Bool
    metricScaleRequired : Bool
    metricScaleRequirementPaid : Bool
    clockBoundPaid : Bool
    rollingShutterBoundPaid : Bool
    reprojectionBoundPaid : Bool
    adequateForThisConsumer : Bool

open PoseConsumerAdequacy public

consumerIndexedBoundary : Consumer.ConsumerIndexedModelBoundary
consumerIndexedBoundary = Consumer.canonicalConsumerIndexedModelBoundary

------------------------------------------------------------------------
-- PRODUCER PARITY
--
-- The known-pose Issue-20 producer and an image-recovered pose may share the
-- same downstream CameraObservation/ray/voxel consumer contract once metric
-- scale is paid.  Contract parity is not evidence-quality parity and does not
-- erase provenance.
------------------------------------------------------------------------

record PoseProducerParity : Set where
  constructor pose-producer-parity
  field
    sameCameraObservationCarrier : Bool
    sameRayProjectionConsumer : Bool
    sameVoxelSurfelGovernanceConsumer : Bool
    provenanceDistinguishesKnownFromRecovered : Bool
    metricScaleRequiredForWorldGridParity : Bool
    numericalPoseEqualityRequired : Bool
    equalEvidenceQualityClaimed : Bool

open PoseProducerParity public

currentPoseProducerParity : PoseProducerParity
currentPoseProducerParity =
  pose-producer-parity
    true
    true
    true
    true
    true
    false
    false

data SameConsumerContractImpliesEqualEvidenceQualityPermission : Set where

data ScaleFreeRelativePoseImpliesMetricWorldParityPermission : Set where

data SyntheticRecoveryImpliesHandheldFieldValidationPermission : Set where

sameConsumerContractDoesNotEqualiseEvidenceQuality :
  SameConsumerContractImpliesEqualEvidenceQualityPermission → ⊥
sameConsumerContractDoesNotEqualiseEvidenceQuality ()

scaleFreeRelativePoseDoesNotEnterMetricWorldByItself :
  ScaleFreeRelativePoseImpliesMetricWorldParityPermission → ⊥
scaleFreeRelativePoseDoesNotEnterMetricWorldByItself ()

syntheticRecoveryDoesNotValidateHandheldFieldUse :
  SyntheticRecoveryImpliesHandheldFieldValidationPermission → ⊥
syntheticRecoveryDoesNotValidateHandheldFieldUse ()

------------------------------------------------------------------------
-- Implementation receipts are kept separate from empirical validation.  The
-- controlled perturbation and calibrated two-view recovery producers now
-- exist in the Animalexic runtime, but the real Issue-20 archive and handheld
-- phone trajectories still owe their empirical validation receipts.
------------------------------------------------------------------------

record PoseRecoveryImplementationStatus : Set where
  constructor pose-recovery-implementation-status
  field
    controlledPerturbationProducerImplemented : Bool
    staticCorrespondenceRecoveryImplemented : Bool
    dynamicTrackMaskImplemented : Bool
    metricScaleGateImplemented : Bool
    cameraObservationParityAdapterImplemented : Bool
    syntheticRecoveryProbePaid : Bool
    issue20ArchiveRecoveryValidated : Bool
    handheldPhoneTrajectoryValidated : Bool

open PoseRecoveryImplementationStatus public

currentPoseRecoveryImplementationStatus : PoseRecoveryImplementationStatus
currentPoseRecoveryImplementationStatus =
  pose-recovery-implementation-status
    true
    true
    true
    true
    true
    true
    false
    false

------------------------------------------------------------------------
-- Regime ladder retained explicitly so known-pose Issue-20 execution cannot
-- collapse directly into handheld success.  The first three rungs now have
-- executable producers; later rungs remain unpaid.
------------------------------------------------------------------------

record MultiCameraPoseRoadmap : Set where
  constructor multi-camera-pose-roadmap
  field
    knownPoseMultiCamera : Bool
    perturbedKnownPose : Bool
    imageRecoveredRelativePose : Bool
    visualInertialTrajectory : Bool
    crossCameraWorldWeld : Bool
    independentClockAlignment : Bool
    rollingShutterCompensation : Bool
    fullyHandheldFusion : Bool

open MultiCameraPoseRoadmap public

currentPoseRoadmap : MultiCameraPoseRoadmap
currentPoseRoadmap =
  multi-camera-pose-roadmap
    true
    true
    true
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Runtime references only; citation/import is not proof of empirical success.
------------------------------------------------------------------------

runtimePoseFibreReference : String
runtimePoseFibreReference = "chboishabba/animalexic/scripts/camera_pose_fibre.py"

sourceIssueReference : String
sourceIssueReference = "ConsistentlyInconsistentYT/Pixeltovoxelprojector#23"
