module DASHI.Cognition.PNF.SensibLawSourceCorrespondenceReviewExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import DASHI.Cognition.PNF.SensibLawReviewWorkstationExact
  using (ReviewItemKind; sourceCorrespondence; ReviewStatus;
         pending; accepted; abstained;
         ReviewAction; accept; reject; abstain; qualify; supersede;
         requestEvidence; openSource; nextStatus)

------------------------------------------------------------------------
-- M10.4 typed *relation*-review boundary, reusing S29 statuses/actions.
-- The two source revisions are never merged into a canonical source.
-- Witness ref must be validated by a runtime owner (PNF or source join).
------------------------------------------------------------------------

data RelationAxis : Set where
  sameSubject sameEvent quotation sourceDependency : RelationAxis

data WitnessClass : Set where
  sharedEntityCandidate sharedEventCandidate nativeSourceJoin : WitnessClass

-- This is a *well-typed witness class*, not an assertion that a
-- candidate relation holds. PNF and provenance operators must independently
-- validate that the particular witness belongs to the selected source pair.
data SupportsAxis : RelationAxis → WitnessClass → Set where
  entityCanNominateSubject :
    SupportsAxis sameSubject sharedEntityCandidate
  eventCanNominateEvent :
    SupportsAxis sameEvent sharedEventCandidate
  nativeJoinCanNominateQuotation :
    SupportsAxis quotation nativeSourceJoin
  nativeJoinCanNominateDependency :
    SupportsAxis sourceDependency nativeSourceJoin

data ObserverAvailability : Set where
  available notObserved unavailable excludedByScope redacted :
    ObserverAvailability

data GenealogyKnowledge : Set where
  noRecordedLineage sourceBackreferenceUnverified independentlyReviewedLineage :
    GenealogyKnowledge

-- The runtime must check 'evidenceRef' belongs to *this* source pair and
-- the required witness class; this record witnesses a validated projection,
-- not a proof that the semantic relation holds in the world.
record CorrespondenceCandidate : Set where
  constructor correspondence-candidate
  field
    leftRevisionRef : String
    rightRevisionRef : String
    relationRef : String
    evidenceRef : String
    consumerScopeRef : String
    axis : RelationAxis
    witnessClass : WitnessClass
    witnessSupportsAxis : SupportsAxis axis witnessClass
    observerAvailability : ObserverAvailability
    genealogy : GenealogyKnowledge
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSourceIdentity : Bool
    createsSourceIdentityIsFalse : createsSourceIdentity ≡ false
    createsEventIdentity : Bool
    createsEventIdentityIsFalse : createsEventIdentity ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    paysEvidence : Bool
    paysEvidenceIsFalse : paysEvidence ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false
    independenceEstablished : Bool
    independenceEstablishedIsFalse : independenceEstablished ≡ false

open CorrespondenceCandidate public

record CorrespondenceReview (candidate : CorrespondenceCandidate) : Set where
  constructor correspondence-review
  field
    reviewItemRef : String
    itemKind : ReviewItemKind
    kindIsCorrespondence : itemKind ≡ sourceCorrespondence
    currentStatus : ReviewStatus
    reviewerRef : String
    reviewCommandRef : String
    action : ReviewAction
    resultingStatus : ReviewStatus
    statusMatchesS29 :
      resultingStatus ≡ nextStatus currentStatus action
    createsSemanticAuthorityAfterReview : Bool
    authorityRemainsFalse :
      createsSemanticAuthorityAfterReview ≡ false
    claimTruthPromotedAfterReview : Bool
    truthRemainsFalse : claimTruthPromotedAfterReview ≡ false
    independenceEstablishedAfterReview : Bool
    independenceRemainsFalse :
      independenceEstablishedAfterReview ≡ false

open CorrespondenceReview public

-- Review *acceptance* is a workflow status, not a source-identity proof
-- or world proposition. These equations are inherited from S29's reducer.
acceptedRelationReviewIsWorkflowOnly :
  nextStatus pending accept ≡ accepted
acceptedRelationReviewIsWorkflowOnly = refl

abstentionPreservesUnknownWorld :
  nextStatus pending abstain ≡ abstained
abstentionPreservesUnknownWorld = refl

openSourceDoesNotChangeRelationStatus :
  ∀ {status} → nextStatus status openSource ≡ status
openSourceDoesNotChangeRelationStatus = refl

------------------------------------------------------------------------
-- Distinct sources, common candidate factors, activity adjacency and
-- quoted text do NOT automatically establish derivation or corroboration.
------------------------------------------------------------------------

data SameWordsProveSameSubject : Set where
data SamePnfProvesSameSource : Set where
data ObserverActivityProvesCopying : Set where
data AcceptedReviewCreatesClaimTruth : Set where
data DistinctRootsProveIndependentEvidence : Set where
data OperationalCarryoverCreatesRelationReview : Set where
data UserScopeExcludedImpliesNotObserved : Set where

sameWordsDoNotEstablishSubject : SameWordsProveSameSubject → ⊥
sameWordsDoNotEstablishSubject ()

pnfCandidateDoesNotMergeSources : SamePnfProvesSameSource → ⊥
pnfCandidateDoesNotMergeSources ()

observerDoesNotEstablishCopying : ObserverActivityProvesCopying → ⊥
observerDoesNotEstablishCopying ()

reviewAcceptanceDoesNotCreateTruth : AcceptedReviewCreatesClaimTruth → ⊥
reviewAcceptanceDoesNotCreateTruth ()

distinctRootsNotSufficient : DistinctRootsProveIndependentEvidence → ⊥
distinctRootsNotSufficient ()

operationalCarryoverNotS29Item : OperationalCarryoverCreatesRelationReview → ⊥
operationalCarryoverNotS29Item ()

scopeExcludedIsNotNoObservation : UserScopeExcludedImpliesNotObserved → ⊥
scopeExcludedIsNotNoObservation ()

-- These are structural, *non-authoritative* fields available to the
-- already-owned S30 Matter projection and Dioxus/wgpu readers.
record M10CorrespondenceProjection : Set where
  constructor m10-correspondence-projection
  field
    matterRef : String
    candidateRelationRefs : List String
    reviewItemRefs : List String
    operationalContextRefs : List String
    sourceTraceRefs : List String
    canonicalWorldMutated : Bool
    worldMutationFalse : canonicalWorldMutated ≡ false
    reviewCreatesTruth : Bool
    truthFalse : reviewCreatesTruth ≡ false

canonicalM10Projection : M10CorrespondenceProjection
canonicalM10Projection =
  m10-correspondence-projection
    "matter:m10" [] [] [] [] false refl false refl
