module DASHI.Biology.AnimalexicSharedWorldGuardTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ANIMALEXIC SHARED-WORLD GUARD TRANSPORT
--
-- This owner closes the representation seam from a candidate world-welded
-- camera trajectory into Animalexic's existing guarded voxel consumer.  It
-- cross-pollinates one structural idea from dashiRTX light transport: compare
-- transported observations against a reference/oracle surface, retain an
-- explicit residual/frontier, and refine the producer that caused consumer-
-- visible error rather than treating a lower transport error as physical truth.
--
-- The domains stay separate: dashiRTX transports radiance/depth observations;
-- Animalexic transports camera-origin/world-point geometry into an existing
-- voxel guard.  No rendering or light-transport claim is imported here.
------------------------------------------------------------------------

record SharedWorldGuardTransportReceipt : Set where
  constructor shared-world-guard-transport-receipt
  field
    runtimeReference : String
    worldWeldedCandidateKeyframeRequired : Bool
    observationCameraIdentityRetained : Bool
    observationTimeIdentityRetained : Bool
    worldPointRetained : Bool
    worldCameraOriginRetained : Bool
    weightRetained : Bool
    residualRetained : Bool
    existingVoxelGuardConsumerReused : Bool
    secondPromotionPathIntroduced : Bool

open SharedWorldGuardTransportReceipt public

currentSharedWorldGuardTransportReceipt : SharedWorldGuardTransportReceipt
currentSharedWorldGuardTransportReceipt =
  shared-world-guard-transport-receipt
    "chboishabba/animalexic/scripts/shared_world_guard_transport.py"
    true
    true
    true
    true
    true
    true
    true
    true
    false

------------------------------------------------------------------------
-- DASHIRTX CROSS-POLLINATION RECEIPT
--
-- The sibling dashiRTX experiment already carries a pinhole pose transport,
-- reprojection error field, signed {-1,0,+1} frontier, importance/state and
-- targeted refinement.  Its roadmap explicitly prefers quality-targeted
-- render -> error -> refine loops.  Animalexic reuses only that architecture:
-- oracle guard -> transport error/frontier -> refine pose/weld evidence.
------------------------------------------------------------------------

record DashiRTXGeometryCrossPollinationReceipt : Set where
  constructor dashi-rtx-geometry-cross-pollination-receipt
  field
    sourceRepository : String
    lightTransportRuntimeReference : String
    ultrametricRuntimeReference : String
    roadmapReference : String
    poseTransportAnalogyRetained : Bool
    signedFrontierAnalogyRetained : Bool
    residualTargetedRefinementAnalogyRetained : Bool
    radianceSemanticsImportedIntoAnimalexic : Bool
    mdlScorePromotedToPhysicalTruth : Bool

open DashiRTXGeometryCrossPollinationReceipt public

currentDashiRTXGeometryCrossPollinationReceipt : DashiRTXGeometryCrossPollinationReceipt
currentDashiRTXGeometryCrossPollinationReceipt =
  dashi-rtx-geometry-cross-pollination-receipt
    "chboishabba/dashiRTX"
    "pda_mdl_light_transport_test.py"
    "quadtree_ultrametric_renderer.py"
    "ROADMAP.md"
    true
    true
    true
    false
    false

------------------------------------------------------------------------
-- Guard transport comparison.
--
-- The runtime emits state agreement, ascended-state IoU, score residual,
-- state-change support and a signed ternary frontier:
--   -1 = candidate state below oracle
--    0 = candidate state agrees with oracle
--   +1 = candidate state above oracle
-- This is a defect/refinement coordinate only.
------------------------------------------------------------------------

record GuardTransportComparisonReceipt : Set where
  constructor guard-transport-comparison-receipt
  field
    stateAgreementMeasured : Bool
    ascendedIoUMeasured : Bool
    scoreResidualMeasured : Bool
    stateChangeMaskRetained : Bool
    signedTernaryFrontierRetained : Bool
    frontierCanScheduleRefinement : Bool
    frontierCanPromoteGeometryByItself : Bool

open GuardTransportComparisonReceipt public

currentGuardTransportComparisonReceipt : GuardTransportComparisonReceipt
currentGuardTransportComparisonReceipt =
  guard-transport-comparison-receipt
    true
    true
    true
    true
    true
    true
    false

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data LowerTransportResidualImpliesCorrectPosePermission : Set where

data BetterAscendedIoUImpliesPhysicalTruthPermission : Set where

data SignedFrontierImpliesPromotionPermission : Set where

data DashiRTXLightTransportImpliesAnimalexicGeometryTruthPermission : Set where

data ObservationPreservingRefinementImpliesProducerIdentityPermission : Set where

lowerTransportResidualDoesNotAutoPayCorrectPose :
  LowerTransportResidualImpliesCorrectPosePermission → ⊥
lowerTransportResidualDoesNotAutoPayCorrectPose ()

betterAscendedIoUDoesNotAutoPayPhysicalTruth :
  BetterAscendedIoUImpliesPhysicalTruthPermission → ⊥
betterAscendedIoUDoesNotAutoPayPhysicalTruth ()

signedFrontierDoesNotAutoPromote :
  SignedFrontierImpliesPromotionPermission → ⊥
signedFrontierDoesNotAutoPromote ()

dashiRTXTransportDoesNotImportGeometryTruth :
  DashiRTXLightTransportImpliesAnimalexicGeometryTruthPermission → ⊥
dashiRTXTransportDoesNotImportGeometryTruth ()

observationPreservingRefinementDoesNotEraseProducerIdentity :
  ObservationPreservingRefinementImpliesProducerIdentityPermission → ⊥
observationPreservingRefinementDoesNotEraseProducerIdentity ()

------------------------------------------------------------------------
-- Implementation / empirical frontier.
------------------------------------------------------------------------

record SharedWorldGuardTransportRoadmapStatus : Set where
  constructor shared-world-guard-transport-roadmap-status
  field
    worldTrajectoryObservationAdapterImplemented : Bool
    actualPerRayWorldOriginsRetained : Bool
    exactExistingGuardConsumerTargeted : Bool
    transportComparisonSurfaceImplemented : Bool
    ternaryFrontierImplemented : Bool
    localFocusedRegressionPaid : Bool
    knownPoseOracleGuardRunPaid : Bool
    recoveredPoseGuardRunPaid : Bool
    robustWeldGuardRunPaid : Bool
    posePerturbationSensitivityCurvePaid : Bool
    sharedWorldVoxelQualityValidated : Bool
    sharedWorldSurfelQualityValidated : Bool
    realMultiphoneValidationPaid : Bool

open SharedWorldGuardTransportRoadmapStatus public

currentSharedWorldGuardTransportRoadmapStatus : SharedWorldGuardTransportRoadmapStatus
currentSharedWorldGuardTransportRoadmapStatus =
  shared-world-guard-transport-roadmap-status
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
    false

record SharedWorldGuardTransportNextResidual : Set where
  constructor shared-world-guard-transport-next-residual
  field
    runKnownPoseOracleThroughGuard : Bool
    runPerturbedPoseThroughGuard : Bool
    runRecoveredPoseThroughGuard : Bool
    runRobustWeldPoseThroughGuard : Bool
    measureStateAndScoreFrontiers : Bool
    attributeFrontierToPoseOrWeldFibre : Bool
    refineOnlyConsumerVisibleDefects : Bool

open SharedWorldGuardTransportNextResidual public

currentSharedWorldGuardTransportNextResidual : SharedWorldGuardTransportNextResidual
currentSharedWorldGuardTransportNextResidual =
  shared-world-guard-transport-next-residual
    true true true true true true true
