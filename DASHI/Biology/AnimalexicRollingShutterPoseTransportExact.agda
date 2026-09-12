module DASHI.Biology.AnimalexicRollingShutterPoseTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROLLING-SHUTTER ROW-TIME POSE TRANSPORT + READOUT CANDIDATE
------------------------------------------------------------------------

record RollingShutterPoseTransportReceipt : Set where
  constructor rolling-shutter-pose-transport-receipt
  field
    runtimeReference : String
    readoutTimeExplicit : Bool
    readoutDirectionExplicit : Bool
    nominalTimestampIsFrameCentre : Bool
    rowTimeOffsetImplemented : Bool
    candidateKeyframeBracketRequired : Bool
    translationInterpolationImplemented : Bool
    SO3RotationInterpolationImplemented : Bool
    outputRemainsCandidate : Bool

open RollingShutterPoseTransportReceipt public

currentRollingShutterPoseTransportReceipt : RollingShutterPoseTransportReceipt
currentRollingShutterPoseTransportReceipt =
  rolling-shutter-pose-transport-receipt
    "chboishabba/animalexic/scripts/rolling_shutter_pose_transport.py"
    true true true true true true true true

record RollingShutterReadoutCandidateReceipt : Set where
  constructor rolling-shutter-readout-candidate-receipt
  field
    rowTimingObservationsRequired : Bool
    rowTimingProvenanceRequired : Bool
    normalizedRowSpanGateImplemented : Bool
    centredLinearTimingFitImplemented : Bool
    readoutMagnitudeCandidateProduced : Bool
    directionCandidateProduced : Bool
    timingResidualGateCanAbstain : Bool
    outputPaysReadoutCalibration : Bool

open RollingShutterReadoutCandidateReceipt public

currentRollingShutterReadoutCandidateReceipt : RollingShutterReadoutCandidateReceipt
currentRollingShutterReadoutCandidateReceipt =
  rolling-shutter-readout-candidate-receipt
    true true true true true true true false

record RollingShutterReadoutPaymentReceipt : Set where
  constructor rolling-shutter-readout-payment-receipt
  field
    exactCandidateReferenceRequired : Bool
    acceptingActorRequired : Bool
    receiptReferenceRequired : Bool
    abstainedCandidateRejected : Bool
    paidReadoutRetainsDirection : Bool
    paidReadoutRetainsMagnitude : Bool
    paymentEqualsFieldValidation : Bool

open RollingShutterReadoutPaymentReceipt public

currentRollingShutterReadoutPaymentReceipt : RollingShutterReadoutPaymentReceipt
currentRollingShutterReadoutPaymentReceipt =
  rolling-shutter-readout-payment-receipt true true true true true true false

data RowTimeTransportImpliesReadoutCalibrationPermission : Set where

data LowRowTimingResidualImpliesReadoutPaymentPermission : Set where

data SuppliedReadoutImpliesFieldRollingShutterValidationPermission : Set where

data InterpolatedRowPoseImpliesPromotedCameraPosePermission : Set where

rowTimeTransportDoesNotEstimateOrPayReadout :
  RowTimeTransportImpliesReadoutCalibrationPermission → ⊥
rowTimeTransportDoesNotEstimateOrPayReadout ()

lowTimingResidualDoesNotAutoPayReadout :
  LowRowTimingResidualImpliesReadoutPaymentPermission → ⊥
lowTimingResidualDoesNotAutoPayReadout ()

suppliedReadoutDoesNotValidateFieldRollingShutter :
  SuppliedReadoutImpliesFieldRollingShutterValidationPermission → ⊥
suppliedReadoutDoesNotValidateFieldRollingShutter ()

interpolatedRowPoseDoesNotPromoteCameraPose :
  InterpolatedRowPoseImpliesPromotedCameraPosePermission → ⊥
interpolatedRowPoseDoesNotPromoteCameraPose ()

record RollingShutterRoadmapStatus : Set where
  constructor rolling-shutter-roadmap-status
  field
    rowTimeTransportImplemented : Bool
    readoutDirectionTransportImplemented : Bool
    rowPoseInterpolationImplemented : Bool
    readoutTimeCandidateEstimatorImplemented : Bool
    readoutDirectionCandidateEstimatorImplemented : Bool
    readoutCandidateAcceptancePaymentImplemented : Bool
    imageResidualRollingShutterValidationPaid : Bool
    realPhoneRollingShutterValidated : Bool

open RollingShutterRoadmapStatus public

currentRollingShutterRoadmapStatus : RollingShutterRoadmapStatus
currentRollingShutterRoadmapStatus =
  rolling-shutter-roadmap-status true true true true true true false false
