module DASHI.Biology.AnimalexicVIOCalibrationCandidatesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- VIO CALIBRATION CANDIDATES + EXPLICIT PAYMENT
------------------------------------------------------------------------

record VIOCalibrationCandidateReceipt : Set where
  constructor vio-calibration-candidate-receipt
  field
    runtimeReference : String
    clockOffsetCandidateImplemented : Bool
    clockResidualMarginGateImplemented : Bool
    ambiguousClockCanAbstain : Bool
    stationaryGyroBiasCandidateImplemented : Bool
    gyroNoiseGateImplemented : Bool
    cameraIMURotationCandidateImplemented : Bool
    noncollinearExcitationRequired : Bool
    cameraIMURotationResidualGateImplemented : Bool
    candidateOutputsAutoPayCalibration : Bool

open VIOCalibrationCandidateReceipt public

currentVIOCalibrationCandidateReceipt : VIOCalibrationCandidateReceipt
currentVIOCalibrationCandidateReceipt =
  vio-calibration-candidate-receipt
    "chboishabba/animalexic/scripts/vio_calibration_candidates.py"
    true true true true true true true true false

record VIOCalibrationPaymentReceipt : Set where
  constructor vio-calibration-payment-receipt
  field
    explicitAcceptanceReceiptRequired : Bool
    exactCoordinateMatchRequired : Bool
    exactCandidateReferenceRequired : Bool
    acceptingActorRequired : Bool
    receiptReferenceRequired : Bool
    abstainedClockCandidateRejected : Bool
    noisyGyroBiasCandidateRejected : Bool
    abstainedExtrinsicCandidateRejected : Bool
    paidClockFeedsExistingCorrectionContract : Bool
    paidExtrinsicFeedsExistingCorrectionContract : Bool
    paidBiasEqualsOnlineBiasOptimization : Bool

open VIOCalibrationPaymentReceipt public

currentVIOCalibrationPaymentReceipt : VIOCalibrationPaymentReceipt
currentVIOCalibrationPaymentReceipt =
  vio-calibration-payment-receipt
    true true true true true true true true true true false

------------------------------------------------------------------------
-- Focused runtime receipt.
------------------------------------------------------------------------

record VIOCalibrationExecutionReceipt : Set where
  constructor vio-calibration-execution-receipt
  field
    exactContentMirrorTests : String
    knownSyntheticClockOffsetRecovered : String
    constantMotionAmbiguityAbstains : Bool
    collinearExtrinsicExcitationRejected : Bool
    exactRepositoryCheckoutExecutionPaid : Bool
    realPhoneCalibrationValidated : Bool

open VIOCalibrationExecutionReceipt public

currentVIOCalibrationExecutionReceipt : VIOCalibrationExecutionReceipt
currentVIOCalibrationExecutionReceipt =
  vio-calibration-execution-receipt
    "11/11 VIO calibration/payment focused tests"
    "-0.2 s"
    true
    true
    false
    false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data LowClockResidualImpliesClockPaymentPermission : Set where

data StationaryBiasCandidateImpliesOnlineBiasOptimizationPermission : Set where

data CameraIMURotationCandidateImpliesFullExtrinsicPermission : Set where

data AcceptedCalibrationImpliesFieldValidationPermission : Set where

lowClockResidualDoesNotAutoPayClock :
  LowClockResidualImpliesClockPaymentPermission → ⊥
lowClockResidualDoesNotAutoPayClock ()

stationaryBiasDoesNotPayOnlineOptimization :
  StationaryBiasCandidateImpliesOnlineBiasOptimizationPermission → ⊥
stationaryBiasDoesNotPayOnlineOptimization ()

rotationCandidateDoesNotPayFullExtrinsic :
  CameraIMURotationCandidateImpliesFullExtrinsicPermission → ⊥
rotationCandidateDoesNotPayFullExtrinsic ()

acceptedCalibrationDoesNotValidateFieldUse :
  AcceptedCalibrationImpliesFieldValidationPermission → ⊥
acceptedCalibrationDoesNotValidateFieldUse ()

------------------------------------------------------------------------
-- Live frontier.
------------------------------------------------------------------------

record VIOCalibrationRoadmapStatus : Set where
  constructor vio-calibration-roadmap-status
  field
    clockOffsetCandidateImplemented : Bool
    stationaryGyroBiasCandidateImplemented : Bool
    cameraIMURotationCandidateImplemented : Bool
    explicitCandidateAcceptanceImplemented : Bool
    paidClockCorrectionHandoffImplemented : Bool
    paidExtrinsicCorrectionHandoffImplemented : Bool
    cameraIMULeverArmEstimationPaid : Bool
    accelerometerBiasEstimationPaid : Bool
    onlineJointCalibrationPaid : Bool
    realPhoneCalibrationValidated : Bool

open VIOCalibrationRoadmapStatus public

currentVIOCalibrationRoadmapStatus : VIOCalibrationRoadmapStatus
currentVIOCalibrationRoadmapStatus =
  vio-calibration-roadmap-status
    true true true true true true false false false false
