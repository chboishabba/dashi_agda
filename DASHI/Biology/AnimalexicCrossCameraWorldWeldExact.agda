module DASHI.Biology.AnimalexicCrossCameraWorldWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ANIMALEXIC CROSS-CAMERA SHARED-WORLD WELD
--
-- Each camera may carry a local time-indexed trajectory L_c.  This owner
-- records the bounded producer that estimates a candidate transform from one
-- local map into another/shared world using shared static 3D anchors.
--
-- Metric local maps use an SE(3) weld.  Scale-uncertain local maps may expose
-- a Sim(3) scale coordinate, but that does not silently pay metric-world scale.
------------------------------------------------------------------------

record WorldWeldProducerReceipt : Set where
  constructor world-weld-producer-receipt
  field
    runtimeReference : String
    sharedStaticAnchorsRequired : Bool
    minimumAnchorCountEnforced : Bool
    degenerateAnchorGeometryRejected : Bool
    rigidSE3ModeImplemented : Bool
    similaritySim3ModeImplemented : Bool
    residualMeasured : Bool
    outputIsCandidateOnly : Bool

open WorldWeldProducerReceipt public

currentWorldWeldProducerReceipt : WorldWeldProducerReceipt
currentWorldWeldProducerReceipt =
  world-weld-producer-receipt
    "chboishabba/animalexic/scripts/cross_camera_world_weld.py"
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Candidate local trajectories may be transported through the weld into a
-- shared target frame without changing their candidate/promotion status.
------------------------------------------------------------------------

record WorldTrajectoryTransportReceipt : Set where
  constructor world-trajectory-transport-receipt
  field
    candidateKeyframesRequired : Bool
    positionTransported : Bool
    orientationTransported : Bool
    velocityTransported : Bool
    similarityScaleAppliedExplicitly : Bool
    transportPromotesTrajectory : Bool

open WorldTrajectoryTransportReceipt public

currentWorldTrajectoryTransportReceipt : WorldTrajectoryTransportReceipt
currentWorldTrajectoryTransportReceipt =
  world-trajectory-transport-receipt
    true
    true
    true
    true
    true
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SharedAnchorsImpliesSameObjectIdentityPermission : Set where

data Sim3AlignmentImpliesMetricScalePaidPermission : Set where

data CandidateWorldWeldImpliesPromotedGlobalTrajectoryPermission : Set where

data LowResidualWeldImpliesFieldHandheldValidationPermission : Set where

sharedAnchorsDoNotAutoPaySameObjectIdentity :
  SharedAnchorsImpliesSameObjectIdentityPermission → ⊥
sharedAnchorsDoNotAutoPaySameObjectIdentity ()

sim3DoesNotAutoPayMetricScale :
  Sim3AlignmentImpliesMetricScalePaidPermission → ⊥
sim3DoesNotAutoPayMetricScale ()

candidateWeldDoesNotAutoPromoteGlobalTrajectory :
  CandidateWorldWeldImpliesPromotedGlobalTrajectoryPermission → ⊥
candidateWeldDoesNotAutoPromoteGlobalTrajectory ()

lowResidualDoesNotAutoValidateHandheldFieldUse :
  LowResidualWeldImpliesFieldHandheldValidationPermission → ⊥
lowResidualDoesNotAutoValidateHandheldFieldUse ()

------------------------------------------------------------------------
-- Exact implementation frontier.
------------------------------------------------------------------------

record CrossCameraWorldWeldRoadmapStatus : Set where
  constructor cross-camera-world-weld-roadmap-status
  field
    rigidWeldProducerImplemented : Bool
    similarityWeldProducerImplemented : Bool
    syntheticRigidRecoveryValidationPaid : Bool
    syntheticSimilarityRecoveryValidationPaid : Bool
    candidateTrajectoryTransportImplemented : Bool
    staticAnchorSameObjectProvenancePaid : Bool
    robustOutlierRejectionPaid : Bool
    temporalAnchorAssociationPaid : Bool
    realMultiPhoneWorldWeldValidated : Bool
    downstreamSharedWorldVoxelFusionValidated : Bool

open CrossCameraWorldWeldRoadmapStatus public

currentCrossCameraWorldWeldRoadmapStatus : CrossCameraWorldWeldRoadmapStatus
currentCrossCameraWorldWeldRoadmapStatus =
  cross-camera-world-weld-roadmap-status
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
