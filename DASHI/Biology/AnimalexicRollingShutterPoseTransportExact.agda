module DASHI.Biology.AnimalexicRollingShutterPoseTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROLLING-SHUTTER ROW-TIME POSE TRANSPORT
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
    suppliedReadoutModelRequired : Bool
    readoutCalibrationEstimated : Bool
    outputRemainsCandidate : Bool

open RollingShutterPoseTransportReceipt public

currentRollingShutterPoseTransportReceipt : RollingShutterPoseTransportReceipt
currentRollingShutterPoseTransportReceipt =
  rolling-shutter-pose-transport-receipt
    "chboishabba/animalexic/scripts/rolling_shutter_pose_transport.py"
    true true true true true true true true false true

data RowTimeTransportImpliesReadoutCalibrationPermission : Set where

data SuppliedReadoutImpliesFieldRollingShutterValidationPermission : Set where

data InterpolatedRowPoseImpliesPromotedCameraPosePermission : Set where

rowTimeTransportDoesNotEstimateReadout :
  RowTimeTransportImpliesReadoutCalibrationPermission → ⊥
rowTimeTransportDoesNotEstimateReadout ()

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
    readoutDirectionImplemented : Bool
    rowPoseInterpolationImplemented : Bool
    readoutTimeCandidateEstimationPaid : Bool
    readoutDirectionCandidateEstimationPaid : Bool
    imageResidualRollingShutterValidationPaid : Bool
    realPhoneRollingShutterValidated : Bool

open RollingShutterRoadmapStatus public

currentRollingShutterRoadmapStatus : RollingShutterRoadmapStatus
currentRollingShutterRoadmapStatus =
  rolling-shutter-roadmap-status true true true false false false false
