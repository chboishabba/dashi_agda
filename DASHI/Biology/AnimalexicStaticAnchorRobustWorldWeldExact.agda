module DASHI.Biology.AnimalexicStaticAnchorRobustWorldWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ANIMALEXIC STATIC-ANCHOR ASSOCIATION + ROBUST WORLD WELD
--
-- This owner sits between upstream landmark/track producers and the existing
-- cross-camera world-weld producer.  Association requires an explicit upstream
-- same-object anchor identity.  It does not promote descriptor similarity,
-- temporal proximity, or geometric fit into object identity.
------------------------------------------------------------------------

record StaticAnchorAssociationReceipt : Set where
  constructor static-anchor-association-receipt
  field
    runtimeReference : String
    exactAnchorIdentityRequired : Bool
    staticEvidenceRequired : Bool
    minimumConfidenceGateImplemented : Bool
    maximumTimeDeltaGateImplemented : Bool
    closestAdmissibleTimestampSelectionImplemented : Bool
    sourceProvenanceRetained : Bool
    targetProvenanceRetained : Bool
    outputIsCandidateOnly : Bool

open StaticAnchorAssociationReceipt public

currentStaticAnchorAssociationReceipt : StaticAnchorAssociationReceipt
currentStaticAnchorAssociationReceipt =
  static-anchor-association-receipt
    "chboishabba/animalexic/scripts/static_anchor_association.py"
    true
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Robust fitting is a bounded consensus layer over already-associated anchors.
-- Minimal 3-anchor hypotheses are tested deterministically, inliers are chosen
-- by an explicit metric residual bound, and the best consensus is refit.
------------------------------------------------------------------------

record RobustWorldWeldReceipt : Set where
  constructor robust-world-weld-receipt
  field
    minimumThreeAnchorHypotheses : Bool
    deterministicHypothesisEnumeration : Bool
    maximumResidualGateImplemented : Bool
    minimumInlierConsensusRequired : Bool
    degenerateHypothesesCanBeRejected : Bool
    consensusRefitImplemented : Bool
    rigidSE3ModeReused : Bool
    similaritySim3ModeReused : Bool
    similarityScaleRemainsExplicit : Bool
    inlierAndOutlierAnchorIDsRetained : Bool
    outputIsCandidateOnly : Bool

open RobustWorldWeldReceipt public

currentRobustWorldWeldReceipt : RobustWorldWeldReceipt
currentRobustWorldWeldReceipt =
  robust-world-weld-receipt
    true
    true
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
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data DescriptorSimilarityImpliesSameObjectIdentityPermission : Set where

data TemporalProximityImpliesSameObjectIdentityPermission : Set where

data GeometricConsensusImpliesSameObjectIdentityPermission : Set where

data RobustWeldImpliesPromotedGlobalGeometryPermission : Set where

data SyntheticRobustFitImpliesFieldMultiphoneValidationPermission : Set where

descriptorSimilarityDoesNotAutoPayIdentity :
  DescriptorSimilarityImpliesSameObjectIdentityPermission → ⊥
descriptorSimilarityDoesNotAutoPayIdentity ()

temporalProximityDoesNotAutoPayIdentity :
  TemporalProximityImpliesSameObjectIdentityPermission → ⊥
temporalProximityDoesNotAutoPayIdentity ()

geometricConsensusDoesNotAutoPayIdentity :
  GeometricConsensusImpliesSameObjectIdentityPermission → ⊥
geometricConsensusDoesNotAutoPayIdentity ()

robustWeldDoesNotAutoPromoteGlobalGeometry :
  RobustWeldImpliesPromotedGlobalGeometryPermission → ⊥
robustWeldDoesNotAutoPromoteGlobalGeometry ()

syntheticRobustFitDoesNotAutoValidateFieldUse :
  SyntheticRobustFitImpliesFieldMultiphoneValidationPermission → ⊥
syntheticRobustFitDoesNotAutoValidateFieldUse ()

------------------------------------------------------------------------
-- Roadmap status.  Runtime implementation is paid.  Exact branch-level test
-- execution and real-phone validation remain separate receipts in environments
-- that can execute the branch and acquire the relevant media.
------------------------------------------------------------------------

record StaticAnchorWorldWeldRoadmapStatus : Set where
  constructor static-anchor-world-weld-roadmap-status
  field
    explicitIdentityAssociationImplemented : Bool
    staticOnlyAssociationImplemented : Bool
    temporalAssociationGateImplemented : Bool
    confidenceGateImplemented : Bool
    deterministicRobustOutlierRejectionImplemented : Bool
    consensusRefitImplemented : Bool
    descriptorBasedAnchorDiscoveryPaid : Bool
    temporalTrackIdentityInferencePaid : Bool
    branchRuntimeRegressionExecuted : Bool
    realMultiphoneAnchorAssociationValidated : Bool
    downstreamSharedWorldVoxelSurfelValidationPaid : Bool

open StaticAnchorWorldWeldRoadmapStatus public

currentStaticAnchorWorldWeldRoadmapStatus : StaticAnchorWorldWeldRoadmapStatus
currentStaticAnchorWorldWeldRoadmapStatus =
  static-anchor-world-weld-roadmap-status
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

------------------------------------------------------------------------
-- Next high-alpha residual: discover/maintain anchor identity without turning
-- descriptor similarity into ontology, then validate world-welded origins in
-- the existing voxel/surfel consumers.
------------------------------------------------------------------------

record StaticAnchorNextResidual : Set where
  constructor static-anchor-next-residual
  field
    discoverAnchorCandidatesFromStaticFeatures : Bool
    retainTrackIdentityAcrossTime : Bool
    attachSameObjectProvenanceReceipt : Bool
    rejectAmbiguousIdentity : Bool
    validateWorldWeldedVoxelOrigins : Bool
    validateWorldWeldedSurfelGeometry : Bool

open StaticAnchorNextResidual public

currentStaticAnchorNextResidual : StaticAnchorNextResidual
currentStaticAnchorNextResidual =
  static-anchor-next-residual true true true true true true
