module DASHI.Interop.SharedUserWorldConsumerRuntimeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SHARED USER/WORLD CONSUMER RUNTIME
--
-- Cross-suite semantic owner for the Smart-Journal / shared-world recurrence:
--
--   bounded sources
--     -> reviewed world coordinates
--     -> consumer dependency slice
--     -> scoped shared-world lookup
--     -> reuse already-paid coordinates OR emit missing work
--     -> reviewed world delta
--     -> recompute affected consumers
--
-- This module is deliberately not legal-specific.  Legal proof search, mission
-- accounting, personal chronology, professional handoff and research are
-- sibling consumers over one provenance-bearing world.
------------------------------------------------------------------------

data SourceLane : Set where
  journalSource : SourceLane
  noteSource : SourceLane
  chatSource : SourceLane
  audioTranscriptSource : SourceLane
  observerCaptureSource : SourceLane
  documentSource : SourceLane
  publicSource : SourceLane
  legalSource : SourceLane
  calendarTaskSource : SourceLane
  professionalSupportSource : SourceLane
  externalEvidenceSource : SourceLane

data WorldCoordinateKind : Set where
  evidenceCoordinate : WorldCoordinateKind
  observationCoordinate : WorldCoordinateKind
  eventCoordinate : WorldCoordinateKind
  claimCoordinate : WorldCoordinateKind
  hypothesisCoordinate : WorldCoordinateKind
  legalAtomCoordinate : WorldCoordinateKind
  authorityCoordinate : WorldCoordinateKind
  missionCoordinate : WorldCoordinateKind
  commitmentCoordinate : WorldCoordinateKind
  absenceCoordinate : WorldCoordinateKind
  conflictCoordinate : WorldCoordinateKind
  residualCoordinate : WorldCoordinateKind
  provenanceCoordinate : WorldCoordinateKind

data ReviewClass : Set where
  observerOnly : ReviewClass
  candidateOnly : ReviewClass
  explicitlyReviewed : ReviewClass
  heldUnresolved : ReviewClass
  excluded : ReviewClass

record SharedWorldCoordinate : Set where
  constructor shared-world-coordinate
  field
    coordinateReference : String
    coordinateKind : WorldCoordinateKind
    sourceLane : SourceLane
    sourceReference : String
    revisionReference : String
    provenanceReference : String
    reviewClass : ReviewClass
    contextEnvelopeReference : String
    shareScopeReference : String
    coordinateCreatesSemanticAuthority : Bool
    coordinateCreatesSemanticAuthorityIsFalse :
      coordinateCreatesSemanticAuthority ≡ false
    coordinateCreatesClaimTruth : Bool
    coordinateCreatesClaimTruthIsFalse :
      coordinateCreatesClaimTruth ≡ false

open SharedWorldCoordinate public

data ConsumerKind : Set where
  personalJournalConsumer : ConsumerKind
  personalTimelineConsumer : ConsumerKind
  missionActualVsShouldConsumer : ConsumerKind
  lawyerMatterConsumer : ConsumerKind
  doctorSupportConsumer : ConsumerKind
  advocateChronologyConsumer : ConsumerKind
  regulatorComplaintConsumer : ConsumerKind
  journalistInvestigationConsumer : ConsumerKind
  legalProofConsumer : ConsumerKind
  historicalResearchConsumer : ConsumerKind
  comparativeConsumer : ConsumerKind
  reportExportConsumer : ConsumerKind

record ConsumerDependencySlice : Set where
  constructor consumer-dependency-slice
  field
    consumerReference : String
    consumerKind : ConsumerKind
    requiredCoordinateReferences : List String
    requiredScopeReference : String
    queryReference : String
    sliceReference : String

open ConsumerDependencySlice public

------------------------------------------------------------------------
-- Reuse is admitted only when an explicit consumer dependency and scope gate
-- both pass and the coordinate has already passed the required review gate.
-- A graph neighbour, matching word or same QID is therefore not itself a join.
------------------------------------------------------------------------

data SharedWorldReuseDisposition : Set where
  reuseAlreadyPaid : SharedWorldReuseDisposition
  researchMissing : SharedWorldReuseDisposition
  scopeBlocked : SharedWorldReuseDisposition

decideSharedWorldReuse :
  Bool -> -- consumer dependency explicitly established
  Bool -> -- consumer scope admits the coordinate
  Bool -> -- required review/payment already exists
  SharedWorldReuseDisposition
decideSharedWorldReuse false _ _ = researchMissing
decideSharedWorldReuse true false _ = scopeBlocked
decideSharedWorldReuse true true false = researchMissing
decideSharedWorldReuse true true true = reuseAlreadyPaid

record SharedWorldLookupReceipt : Set₁ where
  constructor shared-world-lookup-receipt
  field
    consumerSlice : ConsumerDependencySlice
    coordinate : SharedWorldCoordinate
    dependencyEstablished : Bool
    scopeAdmitted : Bool
    reviewRequirementPaid : Bool
    disposition : SharedWorldReuseDisposition
    dispositionMatches :
      disposition ≡
      decideSharedWorldReuse
        dependencyEstablished
        scopeAdmitted
        reviewRequirementPaid
    lookupReference : String

open SharedWorldLookupReceipt public

------------------------------------------------------------------------
-- Reviewed world deltas are cross-consumer facts about the shared carrier.
-- They remain provenance-bearing and non-promoting by construction.
------------------------------------------------------------------------

record ReviewedWorldDelta : Set where
  constructor reviewed-world-delta
  field
    deltaReference : String
    addedCoordinateReferences : List String
    changedCoordinateReferences : List String
    invalidatedCoordinateReferences : List String
    reviewReceiptReference : String
    provenanceReference : String
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open ReviewedWorldDelta public

record AffectedConsumerRecomputation : Set₁ where
  constructor affected-consumer-recomputation
  field
    delta : ReviewedWorldDelta
    affectedConsumerSlices : List ConsumerDependencySlice
    recomputationReference : String
    dependencyIndexed : Bool
    dependencyIndexedIsTrue : dependencyIndexed ≡ true
    recomputationCreatesAuthority : Bool
    recomputationCreatesAuthorityIsFalse :
      recomputationCreatesAuthority ≡ false
    recomputationCreatesTruth : Bool
    recomputationCreatesTruthIsFalse :
      recomputationCreatesTruth ≡ false

open AffectedConsumerRecomputation public

------------------------------------------------------------------------
-- Source revision handling uses the SAME affected-consumer mechanism, but is
-- maintenance/replay rather than the primary discovery recurrence.
------------------------------------------------------------------------

record RevisionMaintenanceDelta : Set where
  constructor revision-maintenance-delta
  field
    coordinateReference : String
    oldRevisionReference : String
    newRevisionReference : String
    affectedObservationReferences : List String
    staleReceiptReferences : List String
    maintenanceReference : String

open RevisionMaintenanceDelta public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameCoordinateMeansSameConsumerOntology : Set where
data SharedWorldAdjacencyEstablishesDependency : Set where
data ObserverCaptureCreatesCanonicalTruth : Set where
data PersonalHypothesisAutomaticallyProfessionalEvidence : Set where
data MissionObservationCreatesMissionTruth : Set where
data ReviewedCoordinateAutomaticallyLegalAuthority : Set where
data ScopeMayBeIgnoredForReuse : Set where
data RevisionChangeIsPrimaryDiscoveryMechanism : Set where
data AffectedConsumerRecomputeCreatesTruth : Set where

sameCoordinateDoesNotCollapseConsumerOntologies :
  SameCoordinateMeansSameConsumerOntology -> ⊥
sameCoordinateDoesNotCollapseConsumerOntologies ()

adjacencyDoesNotEstablishDependency :
  SharedWorldAdjacencyEstablishesDependency -> ⊥
adjacencyDoesNotEstablishDependency ()

observerCaptureDoesNotCreateTruth :
  ObserverCaptureCreatesCanonicalTruth -> ⊥
observerCaptureDoesNotCreateTruth ()

personalHypothesisDoesNotAutoBecomeProfessionalEvidence :
  PersonalHypothesisAutomaticallyProfessionalEvidence -> ⊥
personalHypothesisDoesNotAutoBecomeProfessionalEvidence ()

missionObservationDoesNotCreateMissionTruth :
  MissionObservationCreatesMissionTruth -> ⊥
missionObservationDoesNotCreateMissionTruth ()

reviewedCoordinateDoesNotAutoCreateLegalAuthority :
  ReviewedCoordinateAutomaticallyLegalAuthority -> ⊥
reviewedCoordinateDoesNotAutoCreateLegalAuthority ()

scopeIsMandatoryForReuse : ScopeMayBeIgnoredForReuse -> ⊥
scopeIsMandatoryForReuse ()

revisionMaintenanceIsNotPrimaryDiscovery :
  RevisionChangeIsPrimaryDiscoveryMechanism -> ⊥
revisionMaintenanceIsNotPrimaryDiscovery ()

recomputationDoesNotCreateTruth :
  AffectedConsumerRecomputeCreatesTruth -> ⊥
recomputationDoesNotCreateTruth ()

record SharedUserWorldBoundary : Set where
  constructor shared-user-world-boundary
  field
    consumerQuestionIsPrimaryRecursionUnit : Bool
    consumerQuestionIsPrimaryRecursionUnitIsTrue :
      consumerQuestionIsPrimaryRecursionUnit ≡ true
    sharedWorldLookupPrecedesAcquisition : Bool
    sharedWorldLookupPrecedesAcquisitionIsTrue :
      sharedWorldLookupPrecedesAcquisition ≡ true
    affectedConsumerRecomputationIsDependencyIndexed : Bool
    affectedConsumerRecomputationIsDependencyIndexedIsTrue :
      affectedConsumerRecomputationIsDependencyIndexed ≡ true
    revisionReplayIsSupportingMaintenance : Bool
    revisionReplayIsSupportingMaintenanceIsTrue :
      revisionReplayIsSupportingMaintenance ≡ true
    graphAdjacencyCreatesJoin : Bool
    graphAdjacencyCreatesJoinIsFalse :
      graphAdjacencyCreatesJoin ≡ false
    sameCoordinateCollapsesConsumers : Bool
    sameCoordinateCollapsesConsumersIsFalse :
      sameCoordinateCollapsesConsumers ≡ false

canonicalSharedUserWorldBoundary : SharedUserWorldBoundary
canonicalSharedUserWorldBoundary =
  shared-user-world-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
