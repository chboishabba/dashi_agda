module DASHI.Biology.AnimalexicWorldWeldVoxelOriginHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- WORLD-WELDED CAMERA ORIGIN -> EXISTING VOXEL GUARD
--
-- The existing guarded voxel accumulator historically traced every ray from
-- the world origin.  Regime B needs each observation to retain its actual
-- world-frame camera origin C^W_{c,t}.  The runtime now accepts an optional
-- per-point (N,3) origin fibre while keeping omission exactly backward
-- compatible with the fixed/SBS zero-origin path.
------------------------------------------------------------------------

record VoxelCameraOriginHandoffReceipt : Set where
  constructor voxel-camera-origin-handoff-receipt
  field
    runtimeReference : String
    perPointCameraOriginAccepted : Bool
    oneOriginPerObservedPointRequired : Bool
    finiteOriginCheckImplemented : Bool
    zeroOriginBackwardCompatibilityRetained : Bool
    existingRayWeightingReused : Bool
    existingTemporalEvidenceReused : Bool
    existingResidualWeightingReused : Bool
    existingGuardThresholdsUnchanged : Bool
    canonicalPromotionStillOwnedByExistingGuard : Bool

open VoxelCameraOriginHandoffReceipt public

currentVoxelCameraOriginHandoffReceipt : VoxelCameraOriginHandoffReceipt
currentVoxelCameraOriginHandoffReceipt =
  voxel-camera-origin-handoff-receipt
    "chboishabba/animalexic/scripts/voxel_guard.py"
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
-- WrongType / promotion boundaries.
------------------------------------------------------------------------

data CorrectCameraOriginImpliesCorrectWorldWeldPermission : Set where

data WorldWeldedRaySupportImpliesVoxelPromotionPermission : Set where

data OriginCarrierParityImpliesSharedWorldQualityValidationPermission : Set where

correctOriginDoesNotAutoValidateWorldWeld :
  CorrectCameraOriginImpliesCorrectWorldWeldPermission → ⊥
correctOriginDoesNotAutoValidateWorldWeld ()

worldWeldedRaySupportDoesNotAutoPromoteVoxel :
  WorldWeldedRaySupportImpliesVoxelPromotionPermission → ⊥
worldWeldedRaySupportDoesNotAutoPromoteVoxel ()

originParityDoesNotAutoPayQualityValidation :
  OriginCarrierParityImpliesSharedWorldQualityValidationPermission → ⊥
originParityDoesNotAutoPayQualityValidation ()

------------------------------------------------------------------------
-- Implementation frontier.  The carrier handoff is paid; the end-to-end
-- learned-pose/world-welded voxel and surfel quality experiment is not.
------------------------------------------------------------------------

record WorldWeldVoxelRoadmapStatus : Set where
  constructor world-weld-voxel-roadmap-status
  field
    perRayWorldOriginInterfaceImplemented : Bool
    fixedStereoBackwardCompatibilityImplemented : Bool
    malformedOriginShapeRejected : Bool
    nonfiniteOriginsRejected : Bool
    originWeightingInteroperatesWithExistingFactor : Bool
    learnedPoseWorldOriginsFedEndToEnd : Bool
    robustWeldOriginsFedEndToEnd : Bool
    sharedWorldVoxelQualityValidated : Bool
    sharedWorldSurfelQualityValidated : Bool
    realHandheldMultiphoneValidationPaid : Bool

open WorldWeldVoxelRoadmapStatus public

currentWorldWeldVoxelRoadmapStatus : WorldWeldVoxelRoadmapStatus
currentWorldWeldVoxelRoadmapStatus =
  world-weld-voxel-roadmap-status
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

record WorldWeldVoxelNextResidual : Set where
  constructor world-weld-voxel-next-residual
  field
    adaptWorldTrajectoryAndObservationsIntoGuardInputs : Bool
    compareKnownPoseAndRecoveredPoseVoxelSupport : Bool
    measureWeldResidualVersusVoxelQuality : Bool
    measureOriginPerturbationSensitivity : Bool
    preserveConsumerIndexedPromotionBoundary : Bool

open WorldWeldVoxelNextResidual public

currentWorldWeldVoxelNextResidual : WorldWeldVoxelNextResidual
currentWorldWeldVoxelNextResidual =
  world-weld-voxel-next-residual true true true true true
