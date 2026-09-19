module DASHI.Interop.SLRSprint1AcquisitionMachineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRConsumerRequirementV2Exact as Consumer
import DASHI.Interop.SLRResidualDrivenProducerPlannerExact as Planner
import DASHI.Interop.SLRReviewedEvidencePaymentExact as Review
import DASHI.Interop.SLRBoundedResearchIterationControlExact as Iteration
import DASHI.Interop.SLRGWBPhysicalObjectAcquisitionPolicyExact as Physical
import DASHI.Interop.SLRGWBExecutionRoadmapExact as GWB

------------------------------------------------------------------------
-- SLR SPRINT 1 — RECURRENT ACQUISITION MACHINE
--
-- Golden parity for the production capability:
--
-- Residual
--   -> ProducerPlan
--   -> bounded physical acquisition
--   -> candidate evidence
--   -> explicit review/payment
--   -> W(n+1)
--   -> fresh diagnosis
--   -> repeat
--
-- Restart/replay is semantic infrastructure: the durable receipt chain must
-- reconstruct the same production-relevant world/frontier head before the
-- next hop is selected.
------------------------------------------------------------------------

data Sprint1MilestoneState : Set where
  paid : Sprint1MilestoneState
  implementedAwaitingRuntime : Sprint1MilestoneState
  required : Sprint1MilestoneState

record Sprint1Milestone : Set where
  constructor sprint1Milestone
  field
    milestoneReference : String
    state : Sprint1MilestoneState
    capabilityReference : String
    exitReference : String

open Sprint1Milestone public

sprint1Milestones : List Sprint1Milestone
sprint1Milestones =
    sprint1Milestone
      "M1.1"
      implementedAwaitingRuntime
      "semantic request -> provider resolution -> internal node/source coordinate -> deduplicated physical acquisition plan"
      "P31/P279 specialised slice preferred; route-aware general snapshot is fallback; ordinary path never means all adjacency"
  ∷ sprint1Milestone
      "M1.2"
      implementedAwaitingRuntime
      "cache-aware physical-object transport with pre-concurrency dedupe/coalescing and at most five distinct cold objects per batch"
      "same object x N requests <= one acquisition; cache hit = zero network; six cold objects peak at five; truncation abstains"
  ∷ sprint1Milestone
      "M1.3"
      implementedAwaitingRuntime
      "one producer controller ABI executes classification, identity/source and legal-authority producer families"
      "ConsumerRequirement -> ProducerPlan -> Execution keeps the same controller boundary across all three families"
  ∷ sprint1Milestone
      "M1.4"
      paid
      "reviewed recurrent world expansion with post-hop re-diagnosis and producer-family switching"
      "review is the only semantic payment boundary; rejected/blocked evidence remains receipted; fresh residuals may emerge"
  ∷ sprint1Milestone
      "M1.5"
      implementedAwaitingRuntime
      "restart/replay validation over the durable PostgreSQL adaptive-hop ledger"
      "consecutive hops + prior-receipt chain + world-before(n+1)=world-after(n) reconstruct exact latest production head"
  ∷ []

record CanonicalPhysicalPlanParity : Set where
  constructor physicalPlanParity
  field
    logicalRequestsAreConcurrencyDomain : Bool
    providerResolutionPrecedesScheduling : Bool
    internalNodeOrSourceCoordinateExplicit : Bool
    nodeRouteIndexUsedForGeneralSnapshot : Bool
    physicalObjectIsConcreteShardOrByteRange : Bool
    physicalObjectsDeduplicatedBeforeConcurrency : Bool
    repeatedLogicalRequestsCoalescedByPhysicalObject : Bool
    ordinaryPathLoadsAllAdjacency : Bool
    planIsInspectable : Bool
    planIsReceipted : Bool

open CanonicalPhysicalPlanParity public

canonicalPhysicalPlanParity : CanonicalPhysicalPlanParity
canonicalPhysicalPlanParity =
  physicalPlanParity
    false
    true
    true
    true
    true
    true
    true
    false
    true
    true

record ClassificationProviderOrderParity : Set where
  constructor classificationProviderOrderParity
  field
    specialisedSliceIsFirstTier : Bool
    routeAwareGeneralSnapshotIsSecondTier : Bool
    governedLiveWikidataIsThirdTier : Bool
    specialisedSliceContainsOnlyP31P279 : Bool
    specialisedSliceMissCreatesNegativeOntologyFact : Bool
    generalSnapshotFallbackCountsAsLiveMix : Bool
    actualLiveFallbackRevokesSnapshotSimultaneity : Bool

open ClassificationProviderOrderParity public

canonicalClassificationProviderOrderParity : ClassificationProviderOrderParity
canonicalClassificationProviderOrderParity =
  classificationProviderOrderParity
    true
    true
    true
    true
    false
    false
    true

record BoundedPhysicalTransportParity : Set where
  constructor boundedPhysicalTransportParity
  field
    maxDistinctColdPhysicalObjectsPerBatch : Nat
    cacheHitPerformsNetworkIO : Bool
    physicalDedupeOccursBeforeConcurrency : Bool
    mixedSnapshotLiveMayClaimSimultaneity : Bool
    truncatedObjectMayCreateNegativeOntologyFact : Bool
    truncatedObjectRequiresAbstention : Bool
    receiptTracksLogicalRequests : Bool
    receiptTracksResolvedNodes : Bool
    receiptTracksUniquePhysicalObjects : Bool
    receiptTracksCacheHitsAndMisses : Bool
    receiptTracksCoalescedGets : Bool
    receiptTracksRemoteGets : Bool
    receiptTracksBytes : Bool
    receiptTracksLiveFallbacks : Bool
    receiptTracksPeakColdWidth : Bool
    transportReceiptCreatesSemanticAuthority : Bool

open BoundedPhysicalTransportParity public

canonicalBoundedPhysicalTransportParity : BoundedPhysicalTransportParity
canonicalBoundedPhysicalTransportParity =
  boundedPhysicalTransportParity
    5
    false
    true
    false
    false
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
    false

record GenericProducerControllerParity : Set where
  constructor genericProducerControllerParity
  field
    classificationFamilyReference : String
    identitySourceFamilyReference : String
    authoritySourceFamilyReference : String
    sameControllerABI : Bool
    selectedRouteLowersWithoutProducerReinterpretation : Bool
    acquisitionAutomaticallyPaysResidual : Bool
    evidenceMustRemainCandidateOnly : Bool
    evidenceMayCreateApplicability : Bool
    evidenceMayCreateClaimTruth : Bool

open GenericProducerControllerParity public

canonicalGenericProducerControllerParity : GenericProducerControllerParity
canonicalGenericProducerControllerParity =
  genericProducerControllerParity
    "ClassificationEvidence -> P31/P279"
    "IdentitySource -> Wikidata/persisted identity evidence"
    "AuthoritySource -> governed legal authority/OALC"
    true
    true
    false
    true
    false
    false

record ReviewedRecurrenceParity : Set where
  constructor reviewedRecurrenceParity
  field
    reviewPrecedesSemanticPayment : Bool
    reviewedHopPersistedBeforeNextSelection : Bool
    postHopDiagnosisIsFresh : Bool
    producerFamilyMayChange : Bool
    newResidualsMayOpen : Bool
    rejectedEvidenceRemainsRecorded : Bool
    existingWorldExpansionRunnerIsSourceSinkGeneric : Bool
    gwbSpecificSupervisoryLoopRequired : Bool
    fixedQueueCountsAsAdaptive : Bool
    recurrenceCreatesTruth : Bool

open ReviewedRecurrenceParity public

canonicalReviewedRecurrenceParity : ReviewedRecurrenceParity
canonicalReviewedRecurrenceParity =
  reviewedRecurrenceParity
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false

record RestartReplayParity : Set where
  constructor restartReplayParity
  field
    persistedHopIndexesConsecutive : Bool
    eachNonzeroHopNamesPriorReceipt : Bool
    nextWorldBeforeEqualsPriorWorldAfter : Bool
    replayReconstructsLatestWorldDigest : Bool
    replayReconstructsReceiptHead : Bool
    replayRetainsProducerHistory : Bool
    replayRetainsRejectedOrBlockedOutcomes : Bool
    replayMayAcceptPromotingReceipt : Bool
    continuationRequiresReplayValid : Bool

open RestartReplayParity public

canonicalRestartReplayParity : RestartReplayParity
canonicalRestartReplayParity =
  restartReplayParity
    true
    true
    true
    true
    true
    true
    true
    false
    true

record Sprint1ExitGate : Set where
  constructor sprint1ExitGate
  field
    physicalPlanImplemented : Bool
    boundedTransportImplemented : Bool
    genericProducerExecutionImplemented : Bool
    reviewedRecurrenceImplemented : Bool
    restartReplayImplemented : Bool
    exactRustRuntimeReceiptObserved : Bool
    exactAgdaKernelReceiptObserved : Bool
    sprintMayBeDeclaredClosed : Bool

open Sprint1ExitGate public

currentSprint1ExitGate : Sprint1ExitGate
currentSprint1ExitGate =
  sprint1ExitGate
    true
    true
    true
    true
    true
    false
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GeneralSnapshotMayRunBeforeSpecialisedSlice : Set where
data SliceMissIsOntologyNegation : Set where
data GeneralSnapshotFallbackIsLiveMix : Set where
data LogicalQidCountIsPhysicalConcurrencyBound : Set where
data CacheHitRequiresNetwork : Set where
data RetrievalGapIsOntologyNegation : Set where
data AcquisitionPaysWithoutReview : Set where
data FixedQueueIsAdaptiveRecurrence : Set where
data ReplayMayRewriteWorld : Set where
data TransportCreatesSemanticAuthority : Set where

generalSnapshotCannotPrecedeSpecialisedSlice :
  GeneralSnapshotMayRunBeforeSpecialisedSlice → ⊥
generalSnapshotCannotPrecedeSpecialisedSlice ()

sliceMissDoesNotCreateOntologyNegation :
  SliceMissIsOntologyNegation → ⊥
sliceMissDoesNotCreateOntologyNegation ()

generalSnapshotFallbackIsNotLiveMix :
  GeneralSnapshotFallbackIsLiveMix → ⊥
generalSnapshotFallbackIsNotLiveMix ()

logicalQidCountIsNotPhysicalConcurrencyBound :
  LogicalQidCountIsPhysicalConcurrencyBound → ⊥
logicalQidCountIsNotPhysicalConcurrencyBound ()

cacheHitDoesNotRequireNetwork : CacheHitRequiresNetwork → ⊥
cacheHitDoesNotRequireNetwork ()

retrievalGapDoesNotCreateOntologyNegation :
  RetrievalGapIsOntologyNegation → ⊥
retrievalGapDoesNotCreateOntologyNegation ()

acquisitionCannotPayWithoutReview : AcquisitionPaysWithoutReview → ⊥
acquisitionCannotPayWithoutReview ()

fixedQueueIsNotAdaptiveRecurrence : FixedQueueIsAdaptiveRecurrence → ⊥
fixedQueueIsNotAdaptiveRecurrence ()

replayCannotRewriteWorld : ReplayMayRewriteWorld → ⊥
replayCannotRewriteWorld ()

transportDoesNotCreateSemanticAuthority :
  TransportCreatesSemanticAuthority → ⊥
transportDoesNotCreateSemanticAuthority ()

consumerAnchor : Consumer.ConsumerRequirementV2Parity
consumerAnchor = Consumer.canonicalConsumerRequirementV2Parity

plannerAnchor : Planner.ResidualDrivenProducerPlannerParity
plannerAnchor = Planner.canonicalResidualDrivenProducerPlannerParity

reviewAnchor : Review.ReviewedEvidencePaymentParity
reviewAnchor = Review.canonicalReviewedEvidencePaymentParity

iterationAnchor : Iteration.IterationControlParity
iterationAnchor = Iteration.canonicalIterationControlParity

physicalAnchor : Physical.PhysicalObjectAcquisitionPolicy
physicalAnchor = Physical.canonicalPhysicalObjectAcquisitionPolicy

gwbRoadmapAnchor : List GWB.GWBRoadmapCoordinate
gwbRoadmapAnchor = GWB.gwbSLRRoadmap
