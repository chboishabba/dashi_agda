module DASHI.Biology.AnimalexicIssue20KnownPoseMultiViewExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedModelFibreExact as Fibre

------------------------------------------------------------------------
-- PIXEL-TO-VOXEL ISSUE #20 -> ANIMALEXIC KNOWN-POSE MULTI-VIEW BRIDGE
--
-- This is deliberately a thin formal receipt over existing Animalexic/DASHI
-- machinery.  The runtime producer remains in chboishabba/animalexic.
--
-- The contributed Issue #20 dataset supplies four camera streams together
-- with frame indices and camera position/orientation metadata.  That pays a
-- controlled known-pose multi-camera producer surface.  It does not pay the
-- harder Regime-B problem of recovering time-varying poses from independently
-- drifting cameras.
------------------------------------------------------------------------

record KnownPoseMultiViewProducerReceipt : Set where
  constructor known-pose-multi-view-producer-receipt
  field
    sourceIssueReference : String
    sourceDatasetReference : String
    runtimeProducerReference : String
    cameraPoseMetadataRequired : Bool
    synchronisedFrameIdentityRequired : Bool
    crossCameraSupportRequired : Bool
    outputIsCandidateOnly : Bool
    canonicalPromotionOwnedByGovernance : Bool

open KnownPoseMultiViewProducerReceipt public

issue20KnownPoseProducer : KnownPoseMultiViewProducerReceipt
issue20KnownPoseProducer =
  known-pose-multi-view-producer-receipt
    "ConsistentlyInconsistentYT/Pixeltovoxelprojector#20"
    "xxxdddxxx/PixelToVoxelProjectorInRust/test_data/test_data.tar.xz"
    "chboishabba/animalexic/scripts/issue20_multiview.py"
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Consumer-indexing remains inherited rather than reimplemented here.
------------------------------------------------------------------------

consumerIndexedBoundary : Fibre.ConsumerIndexedModelBoundary
consumerIndexedBoundary = Fibre.canonicalConsumerIndexedModelBoundary

------------------------------------------------------------------------
-- Known-pose success is strictly weaker than opportunistic drifting-camera
-- success.  The latter still owes synchronization, pose recovery / refresh,
-- rolling-shutter handling and shared-world-coordinate validation.
------------------------------------------------------------------------

data KnownPoseFusionImpliesDriftingCameraFusionPermission : Set where

knownPoseFusionDoesNotAutoCloseDriftingCameraFusion :
  KnownPoseFusionImpliesDriftingCameraFusionPermission → ⊥
knownPoseFusionDoesNotAutoCloseDriftingCameraFusion ()

record RegimeBoundary : Set where
  constructor regime-boundary
  field
    knownPoseMultiCameraProducerPaid : Bool
    driftingPoseRecoveryPaid : Bool
    rollingShutterCompensationPaid : Bool
    independentClockAlignmentPaid : Bool
    sameWorldCoordinateValidationPaid : Bool

open RegimeBoundary public

currentIssue20RegimeBoundary : RegimeBoundary
currentIssue20RegimeBoundary =
  regime-boundary
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Runtime meaning:
--
--   frame evidence + known camera model
--     -> world rays
--     -> cross-camera candidate voxel evidence
--     -> existing Animalexic Promote / Abstain governance
--
-- No theorem in this module promotes candidate voxel support directly to a
-- canonical spatial state or to a biological/behavioural interpretation.
------------------------------------------------------------------------

record CandidateOnlyBoundary : Set where
  constructor candidate-only-boundary
  field
    rayIntersectionIsCandidateEvidence : Bool
    rayIntersectionIsCanonicalTruth : Bool
    geometryEvidenceImpliesAnimalMeaning : Bool

canonicalCandidateOnlyBoundary : CandidateOnlyBoundary
canonicalCandidateOnlyBoundary =
  candidate-only-boundary true false false
