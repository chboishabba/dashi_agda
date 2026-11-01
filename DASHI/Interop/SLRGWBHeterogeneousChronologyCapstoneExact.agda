module DASHI.Interop.SLRGWBHeterogeneousChronologyCapstoneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as GWB
import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Chronology
import DASHI.Cognition.PNF.SensibLawReviewWorkstationExact as Review

------------------------------------------------------------------------
-- S28.GWB — heterogeneous corpus chronology capstone.
--
-- Existing paid GWB carrier:
--   10 retained/projected documents
--   41,134 sentence candidates
--   41,124 same-document adjacency candidates
--
-- This capstone does NOT reinterpret those sentence/adjacency counts as
-- canonical claims or events.  It adds only an explicitly reviewed bounded
-- overlay:
--
-- retained local source
--   -> exact source span
--   -> M12 persistent statement
--   -> reviewed candidate observation
--   -> reviewed event join
--   -> S28 temporal / proposition / contestation projection
--   -> S29 review queue
--
-- Raw/projected books remain outside the replay handoff.  A live capstone must
-- therefore run where exact retained source material is available.
------------------------------------------------------------------------

data GWBSourceFamily : Set where
  book memoir wikipedia wikidata publicBiography legalPublicLaw otherReviewed :
    GWBSourceFamily

record GWBReviewedStatementSelection : Set where
  constructor gwb-reviewed-statement-selection
  field
    statementKey : String
    documentOrdinal : Nat
    sourceFamily : GWBSourceFamily
    sourceRoleRef : String
    documentRef : String
    sourceRevisionRef : String
    exactSpanRef : String
    literalText : String
    candidatePNFRef : String
    observationRef : String
    parserReceiptRef : String
    reviewReceiptRef : String
    exactSourceSpanPaid : Bool
    exactSourceSpanPaidIsTrue : exactSourceSpanPaid ≡ true
    explicitlyReviewed : Bool
    explicitlyReviewedIsTrue : explicitlyReviewed ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open GWBReviewedStatementSelection public

record GWBReviewedEventJoin : Set where
  constructor gwb-reviewed-event-join
  field
    eventRef : String
    observationRefs : List String
    assemblyReceiptRef : String
    joinBasisRef : String
    explicitlyReviewed : Bool
    explicitlyReviewedIsTrue : explicitlyReviewed ≡ true
    automaticJoin : Bool
    automaticJoinIsFalse : automaticJoin ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open GWBReviewedEventJoin public

record GWBEventTemporalAccount : Set where
  constructor gwb-event-temporal-account
  field
    eventRef : String
    temporalAssertion : Chronology.TemporalAssertion
    sourceRelationshipRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open GWBEventTemporalAccount public

record GWBReviewedMatterCapstone : Set where
  constructor gwb-reviewed-matter-capstone
  field
    matterRef : String
    handoffRef : String
    boundedStatementSelections : List GWBReviewedStatementSelection
    reviewedEventJoins : List GWBReviewedEventJoin
    propositionRoots : List Chronology.PropositionRoot
    reviewItems : List Review.ReviewItem
    reusesM12Trace : Bool
    reusesM12TraceIsTrue : reusesM12Trace ≡ true
    oneMatterScopedChronology : Bool
    oneMatterScopedChronologyIsTrue : oneMatterScopedChronology ≡ true
    rawBooksEmbeddedInHandoff : Bool
    rawBooksEmbeddedInHandoffIsFalse : rawBooksEmbeddedInHandoff ≡ false
    automaticEventMiningEnabled : Bool
    automaticEventMiningEnabledIsFalse : automaticEventMiningEnabled ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open GWBReviewedMatterCapstone public

------------------------------------------------------------------------
-- Existing GWB scale is retained only as an input carrier fact.
------------------------------------------------------------------------

gwbCandidateWorldAnchor : GWB.GWBCandidateWorldBoundary
gwbCandidateWorldAnchor = GWB.canonicalGWBCandidateWorldBoundary

record GWBCapstoneScaleBoundary : Set where
  constructor gwb-capstone-scale-boundary
  field
    retainedDocumentCount : Nat
    sentenceCandidateCount : Nat
    structuralAdjacencyCount : Nat
    sentenceCandidatesAreCanonicalClaims : Bool
    structuralAdjacencyCreatesEvents : Bool
    rawTextEmbeddedInCandidateWorld : Bool

canonicalGWBCapstoneScaleBoundary : GWBCapstoneScaleBoundary
canonicalGWBCapstoneScaleBoundary =
  gwb-capstone-scale-boundary
    10
    41134
    41124
    false
    false
    false

------------------------------------------------------------------------
-- Multiple source accounts can support one reviewed event without becoming
-- one synthetic narrative.
------------------------------------------------------------------------

record SharedEventAccountBoundary : Set where
  constructor shared-event-account-boundary
  field
    oneReviewedEventIdentity : Bool
    multipleSourceBoundObservations : Bool
    multipleTemporalAssertions : Bool
    multipleClaimLeaves : Bool
    mergedSyntheticNarrative : Bool

canonicalSharedEventAccountBoundary : SharedEventAccountBoundary
canonicalSharedEventAccountBoundary =
  shared-event-account-boundary true true true true false

------------------------------------------------------------------------
-- Two temporal graphs are different projections over the same world:
-- event time versus source/knowledge/revision time.
------------------------------------------------------------------------

data GWBTimeProjectionKind : Set where
  eventTime sourceKnowledgeTime : GWBTimeProjectionKind

record GWBTimeProjectionBoundary : Set where
  constructor gwb-time-projection-boundary
  field
    eventTimeProjectionAvailable : Bool
    sourceKnowledgeTimeProjectionAvailable : Bool
    eventTimeEqualsPublicationTime : Bool
    sourceRevisionMeansWorldChange : Bool

canonicalGWBTimeProjectionBoundary : GWBTimeProjectionBoundary
canonicalGWBTimeProjectionBoundary =
  gwb-time-projection-boundary true true false false

------------------------------------------------------------------------
-- Empirical gate.
------------------------------------------------------------------------

data LivePostgresCapstoneReceiptState : Set where
  sourceWritten awaitingLivePostgres livePostgresPaid :
    LivePostgresCapstoneReceiptState

record GWBCapstoneEmpiricalGate : Set where
  constructor gwb-capstone-empirical-gate
  field
    manifestValidation : LivePostgresCapstoneReceiptState
    exactSourceSliceValidation : LivePostgresCapstoneReceiptState
    m12EventSourceTrace : LivePostgresCapstoneReceiptState
    s28TimelineProjection : LivePostgresCapstoneReceiptState
    s29ReviewQueueProjection : LivePostgresCapstoneReceiptState

canonicalGWBCapstoneEmpiricalGate : GWBCapstoneEmpiricalGate
canonicalGWBCapstoneEmpiricalGate =
  gwb-capstone-empirical-gate
    sourceWritten
    awaitingLivePostgres
    awaitingLivePostgres
    awaitingLivePostgres
    awaitingLivePostgres

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CertifiedSentenceIsReviewedStatement : Set where
data SentenceAdjacencyIsReviewedEventJoin : Set where
data SameQIDAutomaticallyJoinsEvent : Set where
data SamePersonDateAutomaticallyJoinsEvent : Set where
data SimilarTextAutomaticallyJoinsEvent : Set where
data SourceFamilyGetsSeparateSemanticPipeline : Set where
data CohesiveChronologyMeansMergedNarrative : Set where
data RelativeTemporalClaimCreatesExactInstant : Set where
data SourceRevisionMeansWorldChanged : Set where
data MatterChronologyIsMandatoryGlobalTimeline : Set where
data CapstoneReviewCreatesClaimTruth : Set where

certifiedSentenceDoesNotBecomeReviewedStatement :
  CertifiedSentenceIsReviewedStatement → ⊥
certifiedSentenceDoesNotBecomeReviewedStatement ()

sentenceAdjacencyDoesNotCreateReviewedEvent :
  SentenceAdjacencyIsReviewedEventJoin → ⊥
sentenceAdjacencyDoesNotCreateReviewedEvent ()

sameQidDoesNotAutomaticallyJoinEvent :
  SameQIDAutomaticallyJoinsEvent → ⊥
sameQidDoesNotAutomaticallyJoinEvent ()

samePersonDateDoesNotAutomaticallyJoinEvent :
  SamePersonDateAutomaticallyJoinsEvent → ⊥
samePersonDateDoesNotAutomaticallyJoinEvent ()

similarTextDoesNotAutomaticallyJoinEvent :
  SimilarTextAutomaticallyJoinsEvent → ⊥
similarTextDoesNotAutomaticallyJoinEvent ()

sourceFamilyDoesNotCreateSeparatePipeline :
  SourceFamilyGetsSeparateSemanticPipeline → ⊥
sourceFamilyDoesNotCreateSeparatePipeline ()

cohesiveChronologyDoesNotMergeNarrative :
  CohesiveChronologyMeansMergedNarrative → ⊥
cohesiveChronologyDoesNotMergeNarrative ()

relativeClaimDoesNotCreateExactInstant :
  RelativeTemporalClaimCreatesExactInstant → ⊥
relativeClaimDoesNotCreateExactInstant ()

sourceRevisionDoesNotMeanWorldChanged :
  SourceRevisionMeansWorldChanged → ⊥
sourceRevisionDoesNotMeanWorldChanged ()

matterChronologyIsNotMandatoryGlobalTimeline :
  MatterChronologyIsMandatoryGlobalTimeline → ⊥
matterChronologyIsNotMandatoryGlobalTimeline ()

capstoneReviewDoesNotCreateClaimTruth :
  CapstoneReviewCreatesClaimTruth → ⊥
capstoneReviewDoesNotCreateClaimTruth ()
