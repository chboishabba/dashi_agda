module DASHI.Biology.AnimalexicVisualInertialPosePriorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ANIMALEXIC VISUAL-INERTIAL POSE PRIOR
--
-- This owner records the IMU preintegration rung of Regime B.  It is a
-- candidate producer over a time interval, not a claim that full VIO/SLAM or
-- a promoted handheld trajectory is already implemented.
------------------------------------------------------------------------

record IMUPreintegrationReceipt : Set where
  constructor imu-preintegration-receipt
  field
    runtimeReference : String
    timestampsStrictlyOrdered : Bool
    gyroBiasCoordinatePresent : Bool
    accelBiasCoordinatePresent : Bool
    gravityCoordinatePresent : Bool
    rotationDeltaProduced : Bool
    velocityDeltaProduced : Bool
    positionDeltaProduced : Bool
    outputIsCandidateOnly : Bool

open IMUPreintegrationReceipt public

currentIMUPreintegrationReceipt : IMUPreintegrationReceipt
currentIMUPreintegrationReceipt =
  imu-preintegration-receipt
    "chboishabba/animalexic/scripts/visual_inertial_pose.py"
    true
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Visual agreement is a gate on the inertial prior, not an automatic
-- promotion rule and not a replacement for visual relative-pose evidence.
------------------------------------------------------------------------

record VisualInertialConsistencyBoundary : Set where
  constructor visual-inertial-consistency-boundary
  field
    rotationDisagreementMeasured : Bool
    thresholdGateImplemented : Bool
    agreementPromotesTrajectoryByItself : Bool
    imuReplacesVisualPoseRecovery : Bool

open VisualInertialConsistencyBoundary public

currentVisualInertialConsistencyBoundary : VisualInertialConsistencyBoundary
currentVisualInertialConsistencyBoundary =
  visual-inertial-consistency-boundary true true false false

data IMUPreintegrationImpliesAuthoritativeTrajectoryPermission : Set where

data VisualIMUAgreementImpliesPromotedTrajectoryPermission : Set where

data MetricIMUDeltaImpliesDriftFreeScalePermission : Set where

imuPreintegrationDoesNotAutoPromoteTrajectory :
  IMUPreintegrationImpliesAuthoritativeTrajectoryPermission → ⊥
imuPreintegrationDoesNotAutoPromoteTrajectory ()

visualIMUAgreementDoesNotAutoPromoteTrajectory :
  VisualIMUAgreementImpliesPromotedTrajectoryPermission → ⊥
visualIMUAgreementDoesNotAutoPromoteTrajectory ()

metricIMUDeltaDoesNotAutoPayDriftFreeScale :
  MetricIMUDeltaImpliesDriftFreeScalePermission → ⊥
metricIMUDeltaDoesNotAutoPayDriftFreeScale ()

------------------------------------------------------------------------
-- Implementation status: the prior producer exists; the actual VIO trajectory
-- still owes visual correction, camera/IMU extrinsic calibration, time-offset
-- estimation, bias estimation and multi-keyframe optimization.
------------------------------------------------------------------------

record VisualInertialRoadmapStatus : Set where
  constructor visual-inertial-roadmap-status
  field
    imuPreintegrationImplemented : Bool
    syntheticRestValidationPaid : Bool
    syntheticRotationValidationPaid : Bool
    syntheticMetricDeltaValidationPaid : Bool
    visualRotationConsistencyGateImplemented : Bool
    cameraIMUExtrinsicCalibrationPaid : Bool
    cameraIMUClockOffsetPaid : Bool
    onlineBiasEstimationPaid : Bool
    visualKeyframeCorrectionPaid : Bool
    multiKeyframeTrajectoryOptimizationPaid : Bool
    handheldPhoneTrajectoryValidated : Bool

open VisualInertialRoadmapStatus public

currentVisualInertialRoadmapStatus : VisualInertialRoadmapStatus
currentVisualInertialRoadmapStatus =
  visual-inertial-roadmap-status
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
