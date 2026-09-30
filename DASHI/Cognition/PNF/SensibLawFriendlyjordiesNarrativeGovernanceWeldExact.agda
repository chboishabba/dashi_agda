module DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact where

------------------------------------------------------------------------
-- Friendlyjordies / competing-narrative / governance weld.
--
-- This module composes already-existing SensibLaw semantic owners:
--
--   source revision/span
--     -> persistent statement
--     -> claim/proposition leaf
--     -> attribution/occurrence status
--     -> typed contestation between non-collapsed narrative lanes
--     -> review/evidence state
--     -> governance evidence input
--
-- It does NOT decide which political narrative is correct and it does NOT
-- promote a media assertion, review state, or narrative comparison to truth.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Contest
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawReviewWorkstationExact as Review
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Core.GovernanceTrajectoryRealisationExact as Governance

------------------------------------------------------------------------
-- Narrative lane carrier.
------------------------------------------------------------------------

data NarrativeLaneKind : Set where
  sourceNarrative counterNarrative corroborationNarrative : NarrativeLaneKind
  unresolvedNarrative : NarrativeLaneKind

record NarrativeLane : Set where
  constructor narrative-lane
  field
    laneRef : String
    laneKind : NarrativeLaneKind
    sourceRefs : List String
    propositionRefs : List String
    claimRefs : List String
    argumentFamilyRefs : List String
    traceRefs : List String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsCanonicalStory : Bool
    createsCanonicalStoryIsFalse : createsCanonicalStory ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open NarrativeLane public

------------------------------------------------------------------------
-- Source-bound claim occurrence.
------------------------------------------------------------------------

record SourceBoundClaimOccurrence
    (root : Contest.PropositionRoot)
    (leaf : Contest.ClaimLeaf root) : Set where
  constructor source-bound-claim-occurrence
  field
    trace : Trace.SemanticTracePath
    propositionRefMatches :
      Contest.PropositionRoot.propositionRef root
      ≡ Trace.SemanticTracePath.claimRefs trace
        |> firstOr (Contest.PropositionRoot.propositionRef root)
    claimRefPresentAsCoordinate : String
    attributionStatus : Status.PropositionStatusProduct
    occurrenceStatus : Status.EventStatusProduct
    reviewRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsTruth : Bool
    createsTruthIsFalse : createsTruth ≡ false

-- A tiny total helper lets the record state an explicit first-claim coordinate
-- without pretending list membership has been proved by a raw String receipt.
firstOr : ∀ {A : Set} → A → List A → A
firstOr fallback [] = fallback
firstOr fallback (x ∷ xs) = x

infixl 1 _|>_
_|>_ : ∀ {A B : Set} → A → (A → B) → B
x |> f = f x

open SourceBoundClaimOccurrence public

------------------------------------------------------------------------
-- Better proof-relevant source binding.
--
-- Rather than relying on String membership, this owner provides a canonical
-- constructor for traces whose first claim coordinate is the proposition root.
------------------------------------------------------------------------

record RootedTraceClaim
    (root : Contest.PropositionRoot)
    (leaf : Contest.ClaimLeaf root) : Set where
  constructor rooted-trace-claim
  field
    trace : Trace.SemanticTracePath
    leadingClaimRef :
      firstOr
        (Contest.PropositionRoot.propositionRef root)
        (Trace.SemanticTracePath.claimRefs trace)
      ≡ Contest.PropositionRoot.propositionRef root
    leafClaimRef : String
    leafClaimRefMatches :
      leafClaimRef ≡ Contest.ClaimLeaf.claimRef leaf
    sourceRevisionRef : String
    sourceRevisionMatches :
      sourceRevisionRef
      ≡ Trace.PersistentStatementIdentity.sourceRevisionRef
          (Trace.SemanticTracePath.statement trace)
    exactSpanRef : String
    exactSpanMatches :
      exactSpanRef
      ≡ Trace.PersistentStatementIdentity.exactSpanRef
          (Trace.SemanticTracePath.statement trace)

open RootedTraceClaim public

------------------------------------------------------------------------
-- Attribution wrappers.
--
-- SensibLaw already separates "X asserts P" from P and from event occurrence.
-- This wrapper keeps that distinction available inside a narrative lane.
------------------------------------------------------------------------

record NarrativeAttribution
    (claim : Ontology.Claim)
    (perspective : Ontology.Perspective)
    (event : Ontology.Event) : Set where
  constructor narrative-attribution
  field
    weld : Attribution.ClaimAttributionOccurrenceWeld claim perspective event
    sourceStatementRef : String
    embeddedPropositionRef : String
    attributionWrapperRef : String
    embeddedTruthPromoted : Bool
    embeddedTruthPromotedIsFalse : embeddedTruthPromoted ≡ false
    occurrencePromoted : Bool
    occurrencePromotedIsFalse : occurrencePromoted ≡ false

open NarrativeAttribution public

------------------------------------------------------------------------
-- Competing narrative comparison.
------------------------------------------------------------------------

data NarrativeComparisonKind : Set where
  sharedProposition : NarrativeComparisonKind
  leftOnlyProposition : NarrativeComparisonKind
  rightOnlyProposition : NarrativeComparisonKind
  conflictingAccounts : NarrativeComparisonKind
  reasoningFlowDifference : NarrativeComparisonKind
  unresolvedComparison : NarrativeComparisonKind

record NarrativeComparisonItem : Set where
  constructor narrative-comparison-item
  field
    comparisonRef : String
    kind : NarrativeComparisonKind
    leftPropositionRef : String
    rightPropositionRef : String
    contestationRef : String
    sourceRefs : List String
    reviewRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    collapsesNarratives : Bool
    collapsesNarrativesIsFalse : collapsesNarratives ≡ false
    decidesTruth : Bool
    decidesTruthIsFalse : decidesTruth ≡ false

open NarrativeComparisonItem public

record CompetingNarratives : Set where
  constructor competing-narratives
  field
    left : NarrativeLane
    right : NarrativeLane
    comparisonItems : List NarrativeComparisonItem
    sharedFactRefs : List String
    unresolvedRefs : List String
    sourceLocalReceipts : List String
    canonicalMergedStoryCreated : Bool
    canonicalMergedStoryCreatedIsFalse :
      canonicalMergedStoryCreated ≡ false
    hiddenVerdictCreated : Bool
    hiddenVerdictCreatedIsFalse :
      hiddenVerdictCreated ≡ false

open CompetingNarratives public

------------------------------------------------------------------------
-- Typed contestation bridge.
------------------------------------------------------------------------

record ClaimPairContestation
    {rootA rootB : Contest.PropositionRoot}
    (leftClaim : Contest.ClaimLeaf rootA)
    (rightClaim : Contest.ClaimLeaf rootB) : Set where
  constructor claim-pair-contestation
  field
    relation :
      Contest.ContestationRelation leftClaim rightClaim
    comparisonItem : NarrativeComparisonItem
    relationRefMatches :
      NarrativeComparisonItem.contestationRef comparisonItem
      ≡ Contest.ContestationRelation.relationRef relation

open ClaimPairContestation public

------------------------------------------------------------------------
-- Review remains workflow state, not truth.
------------------------------------------------------------------------

record NarrativeReviewBinding : Set where
  constructor narrative-review-binding
  field
    comparisonItem : NarrativeComparisonItem
    reviewItem : Review.ReviewItem
    sameSemanticReference :
      Review.ReviewItem.semanticRef reviewItem
      ≡ NarrativeComparisonItem.comparisonRef comparisonItem
    reviewCreatesTruth : Bool
    reviewCreatesTruthIsFalse : reviewCreatesTruth ≡ false

open NarrativeReviewBinding public

narrativeReviewCannotPromoteTruth :
  Review.ReviewAcceptanceCreatesTruth → ⊥
narrativeReviewCannotPromoteTruth = Review.acceptanceDoesNotCreateTruth

------------------------------------------------------------------------
-- Projection into the governance evidence layer.
--
-- The projection carries provenance and polarity coordinates only.  It never
-- manufactures a gap ordering or party ranking.
------------------------------------------------------------------------

data NarrativeEvidenceMode : Set where
  directObservation interpretiveComparison counterfactualAnalysis : NarrativeEvidenceMode
  unresolvedEvidence : NarrativeEvidenceMode

modeToGovernanceKind : NarrativeEvidenceMode → Governance.EvidenceKind
modeToGovernanceKind directObservation = Governance.observed
modeToGovernanceKind interpretiveComparison = Governance.interpolated
modeToGovernanceKind counterfactualAnalysis = Governance.counterfactual
modeToGovernanceKind unresolvedEvidence = Governance.speculative

record NarrativeGovernanceEvidence : Set where
  constructor narrative-governance-evidence
  field
    narrativeRef : String
    propositionRef : String
    statementRef : String
    sourceRevisionRef : String
    provenanceRefs : List String
    supportRefs : List String
    counterRefs : List String
    missingRefs : List String
    mode : NarrativeEvidenceMode
    sourceTraceRef : String
    reviewRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsGapOrdering : Bool
    createsGapOrderingIsFalse : createsGapOrdering ≡ false
    createsUniversalRanking : Bool
    createsUniversalRankingIsFalse : createsUniversalRanking ≡ false

open NarrativeGovernanceEvidence public

toGovernanceEvidence :
  NarrativeGovernanceEvidence → Governance.GovernanceEvidence
toGovernanceEvidence e =
  Governance.governance-evidence
    (sourceRevisionRef e)
    (statementRef e)
    (provenanceRefs e)
    (modeToGovernanceKind (mode e))
    (supportRefs e)
    (counterRefs e)
    (missingRefs e)

projectedEvidencePreservesKind :
  (e : NarrativeGovernanceEvidence) →
  Governance.GovernanceEvidence.kind (toGovernanceEvidence e)
  ≡ modeToGovernanceKind (mode e)
projectedEvidencePreservesKind e = refl

projectedEvidencePreservesSupport :
  (e : NarrativeGovernanceEvidence) →
  Governance.GovernanceEvidence.supportRefs (toGovernanceEvidence e)
  ≡ supportRefs e
projectedEvidencePreservesSupport e = refl

projectedEvidencePreservesCounter :
  (e : NarrativeGovernanceEvidence) →
  Governance.GovernanceEvidence.counterRefs (toGovernanceEvidence e)
  ≡ counterRefs e
projectedEvidencePreservesCounter e = refl

------------------------------------------------------------------------
-- Friendlyjordies / SensibLaw named public proving-case atlas.
--
-- These are repository-fixture coordinates, not factual adjudications.
------------------------------------------------------------------------

data FriendlyjordiesArgumentFamily : Set where
  cprsBlocking : FriendlyjordiesArgumentFamily
  woolworthsPriceEffects : FriendlyjordiesArgumentFamily
  governmentCapacity : FriendlyjordiesArgumentFamily
  etsDelayAuthority : FriendlyjordiesArgumentFamily
  fallaciesAndFraming : FriendlyjordiesArgumentFamily

argumentFamilyRef : FriendlyjordiesArgumentFamily → String
argumentFamilyRef cprsBlocking = "cprs_blocking"
argumentFamilyRef woolworthsPriceEffects = "woolworths_price"
argumentFamilyRef governmentCapacity = "government_capacity"
argumentFamilyRef etsDelayAuthority = "ets_delay_authority"
argumentFamilyRef fallaciesAndFraming = "fallacies"

friendlyjordiesSourceLane : NarrativeLane
friendlyjordiesSourceLane =
  narrative-lane
    "sensiblaw:friendlyjordies:source-lane"
    sourceNarrative
    ( "SensibLaw/demo/narrative/friendlyjordies_thread_extract.json"
    ∷ "SensibLaw/demo/narrative/friendlyjordies_chat_arguments.json"
    ∷ "SensibLaw/demo/narrative/friendlyjordies_authority_wrappers.json"
    ∷ [])
    []
    []
    ( argumentFamilyRef cprsBlocking
    ∷ argumentFamilyRef woolworthsPriceEffects
    ∷ argumentFamilyRef governmentCapacity
    ∷ argumentFamilyRef etsDelayAuthority
    ∷ argumentFamilyRef fallaciesAndFraming
    ∷ [])
    []
    true refl
    false refl
    false refl

friendlyjordiesCounterLane : NarrativeLane
friendlyjordiesCounterLane =
  narrative-lane
    "sensiblaw:friendlyjordies:counter-analysis-lane"
    counterNarrative
    ( "SensibLaw/demo/narrative/friendlyjordies_thread_extract.json"
    ∷ "SensibLaw/demo/narrative/friendlyjordies_chat_arguments.json"
    ∷ "ITIR-suite/docs/planning/friendlyjordies_narrative_validation_and_competing_narratives_20260309.md"
    ∷ [])
    []
    []
    ( argumentFamilyRef cprsBlocking
    ∷ argumentFamilyRef woolworthsPriceEffects
    ∷ argumentFamilyRef governmentCapacity
    ∷ argumentFamilyRef etsDelayAuthority
    ∷ argumentFamilyRef fallaciesAndFraming
    ∷ [])
    []
    true refl
    false refl
    false refl

friendlyjordiesCompetingNarratives : CompetingNarratives
friendlyjordiesCompetingNarratives =
  competing-narratives
    friendlyjordiesSourceLane
    friendlyjordiesCounterLane
    []
    []
    ("external corroboration pending per proposition" ∷ [])
    ( "SensibLaw narrative fixture receipts"
    ∷ "ITIR narrative comparison planning receipt"
    ∷ [])
    false refl
    false refl

------------------------------------------------------------------------
-- Hard firewalls inherited from the SensibLaw proving case.
------------------------------------------------------------------------

data SharedPropositionMeansCanonicalTruth : Set where
data RepeatedNarrativeMeansIndependentCorroboration : Set where
data AttributionWrapperMakesEmbeddedClaimTrue : Set where
data NarrativeComparisonCreatesPoliticalRanking : Set where
data GovernanceProjectionCreatesGapOrdering : Set where

sharedPropositionDoesNotMeanCanonicalTruth :
  SharedPropositionMeansCanonicalTruth → ⊥
sharedPropositionDoesNotMeanCanonicalTruth ()

repetitionDoesNotMeanIndependentCorroboration :
  RepeatedNarrativeMeansIndependentCorroboration → ⊥
repetitionDoesNotMeanIndependentCorroboration ()

attributionDoesNotMakeEmbeddedTruth :
  AttributionWrapperMakesEmbeddedClaimTrue → ⊥
attributionDoesNotMakeEmbeddedTruth ()

comparisonDoesNotCreatePoliticalRanking :
  NarrativeComparisonCreatesPoliticalRanking → ⊥
comparisonDoesNotCreatePoliticalRanking ()

projectionDoesNotCreateGapOrdering :
  GovernanceProjectionCreatesGapOrdering → ⊥
projectionDoesNotCreateGapOrdering ()

record FriendlyjordiesNarrativeGovernanceBoundary : Set where
  constructor friendlyjordies-narrative-governance-boundary
  field
    sourceTraceRetained : Bool
    sourceTraceRetainedIsTrue : sourceTraceRetained ≡ true
    attributionSeparatedFromTruth : Bool
    attributionSeparatedFromTruthIsTrue :
      attributionSeparatedFromTruth ≡ true
    competingNarrativesRemainDistinct : Bool
    competingNarrativesRemainDistinctIsTrue :
      competingNarrativesRemainDistinct ≡ true
    reviewSeparatedFromTruth : Bool
    reviewSeparatedFromTruthIsTrue :
      reviewSeparatedFromTruth ≡ true
    governanceProjectionCarriesEvidenceOnly : Bool
    governanceProjectionCarriesEvidenceOnlyIsTrue :
      governanceProjectionCarriesEvidenceOnly ≡ true
    sourceFreePoliticalRanking : Bool
    sourceFreePoliticalRankingIsFalse :
      sourceFreePoliticalRanking ≡ false

canonicalFriendlyjordiesNarrativeGovernanceBoundary :
  FriendlyjordiesNarrativeGovernanceBoundary
canonicalFriendlyjordiesNarrativeGovernanceBoundary =
  friendlyjordies-narrative-governance-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
