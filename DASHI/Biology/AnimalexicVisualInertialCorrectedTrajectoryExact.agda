module DASHI.Biology.AnimalexicVisualInertialCorrectedTrajectoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ANIMALEXIC VISUAL-CORRECTED INERTIAL TRAJECTORY
--
-- Runtime now has one bounded Regime-B correction rung: an IMU preintegrated
-- interval is transformed through a paid camera<-IMU rigid transform, compared
-- with a static-scene visual relative pose, corrected only when residual gates
-- pass, and then composed into a time-indexed candidate camera trajectory.
--
-- This owner deliberately does not identify that candidate path with a fully
-- optimized/promoted VIO or SLAM trajectory.
------------------------------------------------------------------------

record VisualInertialCorrectionReceipt : Set where
  constructor visual-inertial-correction-receipt
  field
    runtimeReference : String
    cameraIMUExtrinsicRequired : Bool
    cameraIMULeverArmIncluded : Bool
    clockAlignmentReceiptRequired : Bool
    visualRotationResidualMeasured : Bool
    visualRotationResidualGateImplemented : Bool
    metricVisualTranslationRequiresPaidScale : Bool
    metricPositionResidualGateAvailable : Bool
    residualFailureCanAbstain : Bool
    outputIsCandidateOnly : Bool

open VisualInertialCorrectionReceipt public

currentVisualInertialCorrectionReceipt : VisualInertialCorrectionReceipt
currentVisualInertialCorrectionReceipt =
  visual-inertial-correction-receipt
    "chboishabba/animalexic/scripts/visual_inertial_pose.py"
    true
    true
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Accepted intervals can be accumulated through SE(3) into a local trajectory.
-- Composition is deterministic transport only; it is not bundle adjustment,
-- smoothing, loop closure, bias optimization, or semantic promotion.
------------------------------------------------------------------------

record CandidateTrajectoryCompositionReceipt : Set where
  constructor candidate-trajectory-composition-receipt
  field
    acceptedSegmentsOnly : Bool
    timeIndexedKeyframesProduced : Bool
    relativeRotationComposed : Bool
    cameraCentreDeltaComposed : Bool
    velocityTransported : Bool
    bundleAdjustmentPerformed : Bool
    loopClosurePerformed : Bool
    onlineBiasOptimizationPerformed : Bool
    outputIsPromotedTrajectory : Bool

open CandidateTrajectoryCompositionReceipt public

currentCandidateTrajectoryCompositionReceipt : CandidateTrajectoryCompositionReceipt
currentCandidateTrajectoryCompositionReceipt =
  candidate-trajectory-composition-receipt
    true
    true
    true
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CorrectedCandidateTrajectoryImpliesPromotedVIOPermission : Set where

data SuppliedExtrinsicImpliesOnlineExtrinsicCalibrationPermission : Set where

data SuppliedClockOffsetImpliesClockOffsetEstimatedPermission : Set where

data VisualRotationCorrectionImpliesBiasOptimizationPermission : Set where

correctedCandidateDoesNotAutoPromoteVIO :
  CorrectedCandidateTrajectoryImpliesPromotedVIOPermission → ⊥
correctedCandidateDoesNotAutoPromoteVIO ()

suppliedExtrinsicDoesNotPayOnlineCalibration :
  SuppliedExtrinsicImpliesOnlineExtrinsicCalibrationPermission → ⊥
suppliedExtrinsicDoesNotPayOnlineCalibration ()

suppliedClockOffsetDoesNotPayClockEstimation :
  SuppliedClockOffsetImpliesClockOffsetEstimatedPermission → ⊥
suppliedClockOffsetDoesNotPayClockEstimation ()

visualCorrectionDoesNotAutoPayBiasOptimization :
  VisualRotationCorrectionImpliesBiasOptimizationPermission → ⊥
visualCorrectionDoesNotAutoPayBiasOptimization ()

------------------------------------------------------------------------
-- Exact implementation / validation frontier.
------------------------------------------------------------------------

record CorrectedTrajectoryRoadmapStatus : Set where
  constructor corrected-trajectory-roadmap-status
  field
    imuPreintegrationProducerImplemented : Bool
    visualRelativePoseProducerImplemented : Bool
    suppliedCameraIMUExtrinsicConsumed : Bool
    suppliedClockAlignmentConsumed : Bool
    visualRotationCorrectionImplemented : Bool
    metricVisualPositionCorrectionImplemented : Bool
    abstentionOnResidualFailureImplemented : Bool
    candidateTrajectoryCompositionImplemented : Bool
    syntheticCorrectionValidationPaid : Bool
    onlineCameraIMUExtrinsicCalibrationPaid : Bool
    cameraIMUClockOffsetEstimationPaid : Bool
    onlineBiasEstimationPaid : Bool
    multiKeyframeOptimizationPaid : Bool
    loopClosurePaid : Bool
    handheldPhoneTrajectoryValidated : Bool

open CorrectedTrajectoryRoadmapStatus public

currentCorrectedTrajectoryRoadmapStatus : CorrectedTrajectoryRoadmapStatus
currentCorrectedTrajectoryRoadmapStatus =
  corrected-trajectory-roadmap-status
    true
    true
    true
    true
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
