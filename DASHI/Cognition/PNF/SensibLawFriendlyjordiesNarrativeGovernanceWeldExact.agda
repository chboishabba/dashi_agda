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
-- Proof-relevant source binding.
--
-- The existing trace carries a list of claim references.  This owner does not
-- turn String membership into a proof.  A downstream producer must supply the
-- exact proposition/leaf coordinates it has independently checked.
------------------------------------------------------------------------

record RootedTraceClaim
    (root : Contest.PropositionRoot)
    (leaf : Contest.ClaimLeaf root) : Set where
  constructor rooted-trace-claim
  field
    trace : Trace.SemanticTracePath
    propositionRefCoordinate : String
    propositionRefMatches :
      propositionRefCoordinate
      ≡ Contest.PropositionRoot.propositionRef root
    leafClaimRef : String
    leafClaimRefMatches :
      leafClaimRef ≡ Contest.ClaimLeaf.claimRef leaf
    traceClaimReferenceReceipt : String
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
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

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

------------------------------------------------------------------------
-- Typed fixture proposition roots and source-local claim leaves.
--
-- These mirror the checked-in SensibLaw narrative fixtures.  They represent
-- what each lane asserts/reports, not the truth of the embedded propositions.
------------------------------------------------------------------------

candidateRoot : String → String → Contest.PropositionRoot
candidateRoot ref label =
  Contest.proposition-root
    ref label
    true refl
    false refl
    false refl
    false refl

candidateLeaf :
  (root : Contest.PropositionRoot) →
  String → String → String →
  Contest.ClaimLeaf root
candidateLeaf root claimRef speakerRef statementRef =
  Contest.claim-leaf
    claimRef
    Contest.affirmation
    speakerRef
    (statementRef ∷ [])
    []
    []
    []
    Contest.unreviewed
    ("review:" ++ claimRef)
    ("trace:" ++ claimRef)
    true refl
    false refl
    false refl
    false refl

cprsBlockingRoot : Contest.PropositionRoot
cprsBlockingRoot =
  candidateRoot
    "prop:cprs-blocking"
    "the Greens blocked the CPRS"

sourceCprsClaim : Contest.ClaimLeaf cprsBlockingRoot
sourceCprsClaim =
  candidateLeaf
    cprsBlockingRoot
    "claim:friendlyjordies:cprs-blocking"
    "speaker:friendlyjordies"
    "jordies_thread_position:u1"

counterCprsClaim : Contest.ClaimLeaf cprsBlockingRoot
counterCprsClaim =
  candidateLeaf
    cprsBlockingRoot
    "claim:counter-analysis:cprs-blocking"
    "speaker:counter-analysis"
    "thread_balanced_analysis:u1"

greensInstabilityRoot : Contest.PropositionRoot
greensInstabilityRoot =
  candidateRoot
    "prop:greens-cprs-instability"
    "blocking the CPRS contributed to climate-policy instability"

coalitionInstabilityRoot : Contest.PropositionRoot
coalitionInstabilityRoot =
  candidateRoot
    "prop:coalition-instability"
    "Coalition opposition contributed to climate-policy instability"

sourceInstabilityClaim : Contest.ClaimLeaf greensInstabilityRoot
sourceInstabilityClaim =
  candidateLeaf
    greensInstabilityRoot
    "claim:friendlyjordies:instability"
    "speaker:friendlyjordies"
    "jordies_case:u2"

counterInstabilityClaim : Contest.ClaimLeaf coalitionInstabilityRoot
counterInstabilityClaim =
  candidateLeaf
    coalitionInstabilityRoot
    "claim:counter-analysis:instability"
    "speaker:counter-analysis"
    "counter_analysis:u2"

majorityCapacityRoot : Contest.PropositionRoot
majorityCapacityRoot =
  candidateRoot
    "prop:majority-government-capacity"
    "majority government supports long-term climate policy"

minorityCapacityRoot : Contest.PropositionRoot
minorityCapacityRoot =
  candidateRoot
    "prop:minority-government-capacity"
    "minority government passed carbon-pricing legislation"

sourceMajorityClaim : Contest.ClaimLeaf majorityCapacityRoot
sourceMajorityClaim =
  candidateLeaf
    majorityCapacityRoot
    "claim:friendlyjordies:majority-capacity"
    "speaker:friendlyjordies"
    "jordies_thread_position:u4"

counterMinorityClaim : Contest.ClaimLeaf minorityCapacityRoot
counterMinorityClaim =
  candidateLeaf
    minorityCapacityRoot
    "claim:counter-analysis:minority-capacity"
    "speaker:counter-analysis"
    "thread_balanced_analysis:u4"

woolworthsImpactRoot : Contest.PropositionRoot
woolworthsImpactRoot =
  candidateRoot
    "prop:woolworths-direct-impact"
    "Woolworths evidence concerns direct grocery or cost pass-through effects"

sourceWoolworthsClaim : Contest.ClaimLeaf woolworthsImpactRoot
sourceWoolworthsClaim =
  candidateLeaf
    woolworthsImpactRoot
    "claim:friendlyjordies:woolworths"
    "speaker:friendlyjordies"
    "jordies_thread_position:u5"

counterWoolworthsClaim : Contest.ClaimLeaf woolworthsImpactRoot
counterWoolworthsClaim =
  candidateLeaf
    woolworthsImpactRoot
    "claim:counter-analysis:woolworths"
    "speaker:counter-analysis"
    "thread_balanced_analysis:u5"

garnautAuthorityRoot : Contest.PropositionRoot
garnautAuthorityRoot =
  candidateRoot
    "prop:garnaut-imperfect-ets-delay"
    "an attributed Garnaut position compares an imperfect ETS with delay"

sourceGarnautClaim : Contest.ClaimLeaf garnautAuthorityRoot
sourceGarnautClaim =
  candidateLeaf
    garnautAuthorityRoot
    "claim:friendlyjordies:garnaut-wrapper"
    "speaker:friendlyjordies"
    "jordies_authority_case:u1"

counterGarnautClaim : Contest.ClaimLeaf garnautAuthorityRoot
counterGarnautClaim =
  candidateLeaf
    garnautAuthorityRoot
    "claim:counter-analysis:garnaut-wrapper"
    "speaker:counter-analysis"
    "counter_authority_analysis:u1"

------------------------------------------------------------------------
-- Comparison items: shared proposition != merged claim; competing explanations
-- and reasoning-flow differences remain separate typed items.
------------------------------------------------------------------------

sharedCprsComparison : NarrativeComparisonItem
sharedCprsComparison =
  narrative-comparison-item
    "cmp:cprs:shared"
    sharedProposition
    (Contest.propositionRef cprsBlockingRoot)
    (Contest.propositionRef cprsBlockingRoot)
    "relation:shared-root-distinct-claims"
    ("jordies_thread_position:u1" ∷ "thread_balanced_analysis:u1" ∷ [])
    "review:cmp:cprs:shared"
    true refl
    false refl
    false refl

instabilityAccountComparison : NarrativeComparisonItem
instabilityAccountComparison =
  narrative-comparison-item
    "cmp:instability:competing-account"
    conflictingAccounts
    (Contest.propositionRef greensInstabilityRoot)
    (Contest.propositionRef coalitionInstabilityRoot)
    "relation:instability:same-incident-different-account"
    ("jordies_case:u2" ∷ "counter_analysis:u2" ∷ [])
    "review:cmp:instability"
    true refl
    false refl
    false refl

instabilityContestation :
  Contest.ContestationRelation sourceInstabilityClaim counterInstabilityClaim
instabilityContestation =
  Contest.contestation-relation
    "relation:instability:same-incident-different-account"
    Contest.sameIncidentDifferentAccount
    ("jordies_case:u2" ∷ "counter_analysis:u2" ∷ [])
    []
    "review:cmp:instability"
    "source-local narrative comparison"
    true refl
    false refl
    false refl
    false refl

instabilityClaimPairContestation :
  ClaimPairContestation sourceInstabilityClaim counterInstabilityClaim
instabilityClaimPairContestation =
  claim-pair-contestation
    instabilityContestation
    instabilityAccountComparison
    refl

governmentCapacityComparison : NarrativeComparisonItem
governmentCapacityComparison =
  narrative-comparison-item
    "cmp:government-capacity:reasoning-flow"
    reasoningFlowDifference
    (Contest.propositionRef majorityCapacityRoot)
    (Contest.propositionRef minorityCapacityRoot)
    "relation:government-capacity:distinct-reasoning-paths"
    ("jordies_thread_position:u4" ∷ "thread_balanced_analysis:u4" ∷ [])
    "review:cmp:government-capacity"
    true refl
    false refl
    false refl

woolworthsComparison : NarrativeComparisonItem
woolworthsComparison =
  narrative-comparison-item
    "cmp:woolworths:qualification"
    reasoningFlowDifference
    (Contest.propositionRef woolworthsImpactRoot)
    (Contest.propositionRef woolworthsImpactRoot)
    "relation:woolworths:shared-topic-distinct-framing"
    ("jordies_thread_position:u5" ∷ "thread_balanced_analysis:u5" ∷ [])
    "review:cmp:woolworths"
    true refl
    false refl
    false refl

garnautAuthorityComparison : NarrativeComparisonItem
garnautAuthorityComparison =
  narrative-comparison-item
    "cmp:garnaut:authority-wrapper"
    sharedProposition
    (Contest.propositionRef garnautAuthorityRoot)
    (Contest.propositionRef garnautAuthorityRoot)
    "relation:garnaut:shared-attributed-proposition"
    ("jordies_authority_case:u1" ∷ "counter_authority_analysis:u1" ∷ [])
    "review:cmp:garnaut"
    true refl
    false refl
    false refl

friendlyjordiesSourceLane : NarrativeLane
friendlyjordiesSourceLane =
  narrative-lane
    "sensiblaw:friendlyjordies:source-lane"
    sourceNarrative
    ( "SensibLaw/demo/narrative/friendlyjordies_thread_extract.json"
    ∷ "SensibLaw/demo/narrative/friendlyjordies_chat_arguments.json"
    ∷ "SensibLaw/demo/narrative/friendlyjordies_authority_wrappers.json"
    ∷ [])
    ( Contest.propositionRef cprsBlockingRoot
    ∷ Contest.propositionRef greensInstabilityRoot
    ∷ Contest.propositionRef majorityCapacityRoot
    ∷ Contest.propositionRef woolworthsImpactRoot
    ∷ Contest.propositionRef garnautAuthorityRoot
    ∷ [])
    ( Contest.claimRef sourceCprsClaim
    ∷ Contest.claimRef sourceInstabilityClaim
    ∷ Contest.claimRef sourceMajorityClaim
    ∷ Contest.claimRef sourceWoolworthsClaim
    ∷ Contest.claimRef sourceGarnautClaim
    ∷ [])
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
    ( Contest.propositionRef cprsBlockingRoot
    ∷ Contest.propositionRef coalitionInstabilityRoot
    ∷ Contest.propositionRef minorityCapacityRoot
    ∷ Contest.propositionRef woolworthsImpactRoot
    ∷ Contest.propositionRef garnautAuthorityRoot
    ∷ [])
    ( Contest.claimRef counterCprsClaim
    ∷ Contest.claimRef counterInstabilityClaim
    ∷ Contest.claimRef counterMinorityClaim
    ∷ Contest.claimRef counterWoolworthsClaim
    ∷ Contest.claimRef counterGarnautClaim
    ∷ [])
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
    ( sharedCprsComparison
    ∷ instabilityAccountComparison
    ∷ governmentCapacityComparison
    ∷ woolworthsComparison
    ∷ garnautAuthorityComparison
    ∷ [])
    ( Contest.propositionRef cprsBlockingRoot
    ∷ Contest.propositionRef woolworthsImpactRoot
    ∷ Contest.propositionRef garnautAuthorityRoot
    ∷ [])
    ( Contest.propositionRef greensInstabilityRoot
    ∷ Contest.propositionRef coalitionInstabilityRoot
    ∷ Contest.propositionRef majorityCapacityRoot
    ∷ Contest.propositionRef minorityCapacityRoot
    ∷ [])
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
