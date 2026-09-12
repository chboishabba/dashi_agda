module DASHI.Biology.AnimalexicIssue20PoseRecoveryValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ISSUE-20 LEARNED-POSE VALIDATION BOUNDARY
--
-- The runtime may recover relative camera pose from image evidence and then
-- compare that candidate against the known Issue-20 metadata.  The known pose
-- is a post-hoc oracle only: it is not an input to the learned-pose producer.
------------------------------------------------------------------------

record Issue20PoseRecoveryReceipt : Set where
  constructor issue20-pose-recovery-receipt
  field
    sourceRepositoryReference : String
    sourceArchiveBlobReference : String
    runtimeReference : String
    staticFeatureMaskingImplemented : Bool
    calibratedRelativePoseRecoveryImplemented : Bool
    knownPoseConvertedToValidationGeometry : Bool
    knownPoseUsedOnlyForPostHocScoring : Bool
    learnedPoseRemainsScaleFree : Bool
    outputRemainsCandidate : Bool

open Issue20PoseRecoveryReceipt public

issue20PoseRecoveryReceipt : Issue20PoseRecoveryReceipt
issue20PoseRecoveryReceipt =
  issue20-pose-recovery-receipt
    "xxxdddxxx/PixelToVoxelProjectorInRust"
    "git-blob:ab1f9e7a90588c776f4aafe6274f3304f4ed30a6"
    "chboishabba/animalexic/scripts/issue20_pose_recovery.py"
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Acquisition, executable implementation and empirical validation are
-- deliberately separate coordinates.
------------------------------------------------------------------------

record Issue20ArchiveValidationStatus : Set where
  constructor issue20-archive-validation-status
  field
    archiveIdentityKnown : Bool
    archiveBytesAcquiredInExecutionEnvironment : Bool
    archiveImagesDecoded : Bool
    recoveryOperatorImplemented : Bool
    syntheticRenderedImageValidationPaid : Bool
    realArchiveRecoveryExecuted : Bool
    realArchivePoseErrorMeasured : Bool
    downstreamVoxelSurfelDegradationMeasured : Bool

open Issue20ArchiveValidationStatus public

currentIssue20ArchiveValidationStatus : Issue20ArchiveValidationStatus
currentIssue20ArchiveValidationStatus =
  issue20-archive-validation-status
    true
    false
    false
    true
    true
    false
    false
    false

------------------------------------------------------------------------
-- Firewalls: a runnable real-data operator is not the same object as a real
-- archive execution receipt; post-hoc oracle scoring is not data leakage into
-- the pose producer; synthetic rendered validation is not field validation.
------------------------------------------------------------------------

data RealDataCapableOperatorImpliesArchiveExecutionPermission : Set where

data PostHocKnownPoseScoreImpliesKnownPoseWasRecoveryInputPermission : Set where

data RenderedImageValidationImpliesArchiveValidationPermission : Set where

realDataCapableDoesNotAutoPayArchiveExecution :
  RealDataCapableOperatorImpliesArchiveExecutionPermission → ⊥
realDataCapableDoesNotAutoPayArchiveExecution ()

postHocScoreDoesNotMeanKnownPoseEnteredRecovery :
  PostHocKnownPoseScoreImpliesKnownPoseWasRecoveryInputPermission → ⊥
postHocScoreDoesNotMeanKnownPoseEnteredRecovery ()

renderedValidationDoesNotAutoPayArchiveValidation :
  RenderedImageValidationImpliesArchiveValidationPermission → ⊥
renderedValidationDoesNotAutoPayArchiveValidation ()

------------------------------------------------------------------------
-- The next consumer-visible residual is empirical, not representational.
------------------------------------------------------------------------

record Issue20NextResidual : Set where
  constructor issue20-next-residual
  field
    acquireArchiveBytes : Bool
    executePairwiseRecovery : Bool
    measureRotationError : Bool
    measureTranslationDirectionError : Bool
    measureVoxelSurfelSensitivity : Bool

open Issue20NextResidual public

currentIssue20NextResidual : Issue20NextResidual
currentIssue20NextResidual =
  issue20-next-residual true true true true true
