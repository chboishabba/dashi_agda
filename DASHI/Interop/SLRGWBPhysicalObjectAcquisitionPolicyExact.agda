module DASHI.Interop.SLRGWBPhysicalObjectAcquisitionPolicyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBReviewedWikimediaIdentityAndTieredTransportExact as Tiered
import DASHI.Interop.SLRResidualDrivenProducerPlannerExact as Planner

------------------------------------------------------------------------
-- GWB PHYSICAL-OBJECT ACQUISITION POLICY
--
-- Golden contract for the production SLR transport layer.
--
-- Logical QID/name requests are not the concurrency domain.  They are first
-- resolved to a bounded physical acquisition plan.  Concurrency applies only
-- after route selection and physical-object deduplication/coalescing.
--
-- Normal classification route:
--   local/PG/cache
--     -> specialised P31/P279 predicate slice
--     -> route-aware general Zelph/HF snapshot
--     -> live revision-pinned Wikidata when required.
--
-- The route and transport are evidence-production mechanisms only.
------------------------------------------------------------------------

data PhysicalAcquisitionState : Set where
  paid : PhysicalAcquisitionState
  implementedAwaitingRuntime : PhysicalAcquisitionState
  required : PhysicalAcquisitionState

record PhysicalObjectAcquisitionPolicy : Set where
  constructor physicalObjectAcquisitionPolicy
  field
    semanticTargetReference : String
    specialisedPredicateSliceBeforeGeneralAdjacency : Bool
    specialisedPredicateSetReference : String
    generalSnapshotUsesNodeRouteIndex : Bool
    logicalRequestsResolvedBeforeScheduling : Bool
    physicalObjectsDeduplicatedBeforeConcurrency : Bool
    samePhysicalObjectCoalescedWithinSLR : Bool
    cacheHitPerformsZeroNetworkIO : Bool
    maxConcurrentRemoteObjects : Nat
    concurrencyCountsLogicalQids : Bool
    mixedSnapshotLiveMayClaimSimultaneity : Bool
    retrievalGapMeansOntologyNegation : Bool
    snapshotEvidenceCreatesSemanticAuthority : Bool
    liveEvidenceCreatesSemanticAuthority : Bool
    truncationRequiresAbstention : Bool
    transportReceiptRequired : Bool

open PhysicalObjectAcquisitionPolicy public

canonicalPhysicalObjectAcquisitionPolicy : PhysicalObjectAcquisitionPolicy
canonicalPhysicalObjectAcquisitionPolicy =
  physicalObjectAcquisitionPolicy
    "GWB supervised P31/P279 type closure"
    true
    "P31 union P279"
    true
    true
    true
    true
    true
    5
    false
    false
    false
    false
    false
    true
    true

record PhysicalTransportReceiptShape : Set where
  constructor physicalTransportReceiptShape
  field
    requestedSemanticTargetsReference : String
    resolvedInternalNodesReference : String
    selectedSliceOrSnapshotReference : String
    physicalObjectsPlannedReference : String
    cacheHitsReference : String
    cacheMissesReference : String
    coalescedGetsReference : String
    remoteObjectGetsReference : String
    bytesFetchedReference : String
    liveFallbacksReference : String
    closureObservationsReference : String
    receiptCreatesTruth : Bool

open PhysicalTransportReceiptShape public

canonicalPhysicalTransportReceiptShape : PhysicalTransportReceiptShape
canonicalPhysicalTransportReceiptShape =
  physicalTransportReceiptShape
    "requested_qids/semantic_targets"
    "resolved_internal_nodes"
    "selected_predicate_slice_or_snapshot"
    "unique_physical_objects"
    "cache_hits"
    "cache_misses"
    "coalesced_gets"
    "remote_object_gets"
    "bytes_fetched"
    "live_fallbacks"
    "useful_P31_P279_observations"
    false

record SprintATransportGate : Set where
  constructor sprintATransportGate
  field
    predicateSliceProvider : PhysicalAcquisitionState
    routeAwareGeneralHFProvider : PhysicalAcquisitionState
    physicalObjectDeduplication : PhysicalAcquisitionState
    boundedFiveObjectScheduler : PhysicalAcquisitionState
    acquisitionTelemetry : PhysicalAcquisitionState
    cacheSingleFlightInsideZelph : PhysicalAcquisitionState
    singleFlightIsRequiredForSLRSemanticCorrectness : Bool
    transportOptimisationMayContinueAfterGateWithoutObservedNeed : Bool

open SprintATransportGate public

currentSprintATransportGate : SprintATransportGate
currentSprintATransportGate =
  sprintATransportGate
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LogicalQidConcurrencyIsPhysicalBound : Set where
data SnapshotSimultaneitySurvivesLiveFallback : Set where
data RetrievalGapCreatesNegativeOntologyFact : Set where
data PhysicalTransportCreatesSemanticAuthority : Set where
data CacheImplementationDetailCreatesSemanticMeaning : Set where

logicalQidCountIsNotPhysicalBound : LogicalQidConcurrencyIsPhysicalBound → ⊥
logicalQidCountIsNotPhysicalBound ()

mixedTransportDoesNotPreserveSnapshotSimultaneity :
  SnapshotSimultaneitySurvivesLiveFallback → ⊥
mixedTransportDoesNotPreserveSnapshotSimultaneity ()

retrievalGapDoesNotCreateOntologyNegation :
  RetrievalGapCreatesNegativeOntologyFact → ⊥
retrievalGapDoesNotCreateOntologyNegation ()

physicalTransportDoesNotCreateSemanticAuthority :
  PhysicalTransportCreatesSemanticAuthority → ⊥
physicalTransportDoesNotCreateSemanticAuthority ()

cacheMechanicsDoNotCreateSemantics :
  CacheImplementationDetailCreatesSemanticMeaning → ⊥
cacheMechanicsDoNotCreateSemantics ()

tieredTransportAnchor : Tiered.WikidataTieredTransportPolicy
tieredTransportAnchor = Tiered.canonicalWikidataTieredTransportPolicy

plannerAnchor : Planner.ResidualDrivenProducerPlannerParity
plannerAnchor = Planner.canonicalResidualDrivenProducerPlannerParity
