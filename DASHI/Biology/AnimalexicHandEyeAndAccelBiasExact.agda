module DASHI.Biology.AnimalexicHandEyeAndAccelBiasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CAMERA/IMU LEVER ARM + GRAVITY-REFERENCED ACCELEROMETER BIAS
------------------------------------------------------------------------

record HandEyeTranslationCandidateReceipt : Set where
  constructor hand-eye-translation-candidate-receipt
  field
    runtimeReference : String
    pairedSE3MotionsRequired : Bool
    suppliedCameraIMURotationRequired : Bool
    axEqualsXbRotationConsistencyChecked : Bool
    stackedTranslationSystemImplemented : Bool
    fullRankExcitationRequired : Bool
    translationResidualMeasured : Bool
    highResidualCanAbstain : Bool
    candidatePaysLeverArm : Bool

open HandEyeTranslationCandidateReceipt public

currentHandEyeTranslationCandidateReceipt : HandEyeTranslationCandidateReceipt
currentHandEyeTranslationCandidateReceipt =
  hand-eye-translation-candidate-receipt
    "chboishabba/animalexic/scripts/vio_calibration_candidates.py"
    true true true true true true true false

record HandEyeSyntheticReceipt : Set where
  constructor hand-eye-synthetic-receipt
  field
    knownLeverArm : String
    stackedRank : String
    recoveryNormError : String
    residualRMS : String
    pureTranslationRank : String
    repositoryCheckoutExecutionPaid : Bool

open HandEyeSyntheticReceipt public

currentHandEyeSyntheticReceipt : HandEyeSyntheticReceipt
currentHandEyeSyntheticReceipt =
  hand-eye-synthetic-receipt
    "(0.12,-0.04,0.08) m"
    "3"
    "1.2813490069415586e-16 m"
    "2.0217778535881156e-17 m"
    "0"
    false

record AccelerometerBiasCandidateReceipt : Set where
  constructor accelerometer-bias-candidate-receipt
  field
    runtimeReference : String
    stationarySamplesRequired : Bool
    gravityVectorExplicit : Bool
    orientationExplicit : Bool
    expectedSpecificForceIsMinusRTg : Bool
    axisNoiseGateImplemented : Bool
    noisyCandidateCanAbstain : Bool
    candidatePaysOnlineBiasOptimization : Bool

open AccelerometerBiasCandidateReceipt public

currentAccelerometerBiasCandidateReceipt : AccelerometerBiasCandidateReceipt
currentAccelerometerBiasCandidateReceipt =
  accelerometer-bias-candidate-receipt
    "chboishabba/animalexic/scripts/accel_bias_candidate.py"
    true true true true true true false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FullRankHandEyeImpliesFieldExtrinsicTruthPermission : Set where

data SmallTranslationResidualImpliesLeverArmPaymentPermission : Set where

data StationaryAccelMeanImpliesBiasWithoutGravityPermission : Set where

data AccelerometerBiasCandidateImpliesOnlineBiasOptimizationPermission : Set where

fullRankHandEyeDoesNotValidateFieldExtrinsic :
  FullRankHandEyeImpliesFieldExtrinsicTruthPermission → ⊥
fullRankHandEyeDoesNotValidateFieldExtrinsic ()

smallResidualDoesNotAutoPayLeverArm :
  SmallTranslationResidualImpliesLeverArmPaymentPermission → ⊥
smallResidualDoesNotAutoPayLeverArm ()

stationaryAccelMeanDoesNotEraseGravityReference :
  StationaryAccelMeanImpliesBiasWithoutGravityPermission → ⊥
stationaryAccelMeanDoesNotEraseGravityReference ()

accelBiasCandidateDoesNotPayOnlineOptimization :
  AccelerometerBiasCandidateImpliesOnlineBiasOptimizationPermission → ⊥
accelBiasCandidateDoesNotPayOnlineOptimization ()

record CalibrationExtensionRoadmapStatus : Set where
  constructor calibration-extension-roadmap-status
  field
    handEyeLeverArmCandidateImplemented : Bool
    handEyeDegeneracyGateImplemented : Bool
    syntheticLeverArmProbePaid : Bool
    accelerometerBiasCandidateImplemented : Bool
    gravityOrientationReferenceExplicit : Bool
    noisyAccelAbstentionImplemented : Bool
    leverArmAcceptancePaymentImplemented : Bool
    accelerometerBiasAcceptancePaymentImplemented : Bool
    jointOnlineCalibrationPaid : Bool
    realPhoneCalibrationValidated : Bool

open CalibrationExtensionRoadmapStatus public

currentCalibrationExtensionRoadmapStatus : CalibrationExtensionRoadmapStatus
currentCalibrationExtensionRoadmapStatus =
  calibration-extension-roadmap-status
    true true true true true true false false false false
