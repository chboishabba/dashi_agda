module DASHI.Cognition.PNF.SensibLawReviewWorkstationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

------------------------------------------------------------------------
-- S29 portable human-review workstation.
--
-- Review may change review/workflow status or request evidence/navigation.
-- It does not itself create semantic authority, legal applicability, or truth.
------------------------------------------------------------------------

data ReviewItemKind : Set where
  pnfParse observation claimContestation eventAssembly chronologyAmbiguity :
    ReviewItemKind
  authorityFollow researchAcquisition legalTreatment scopeHandoff :
    ReviewItemKind

data ReviewStatus : Set where
  pending accepted rejected abstained qualified superseded needsEvidence :
    ReviewStatus

data ReviewAction : Set where
  accept reject abstain qualify supersede requestEvidence openSource followAuthority :
    ReviewAction

record ReviewItem : Set where
  constructor review-item
  field
    reviewItemRef : String
    semanticRef : String
    itemKind : ReviewItemKind
    reason : String
    provenanceRefs : List String
    sourceRefs : List String
    currentStatus : ReviewStatus
    availableActions : List ReviewAction
    affectedConsumerRefs : List String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ReviewItem public

nextStatus : ReviewStatus → ReviewAction → ReviewStatus
nextStatus _ accept = accepted
nextStatus _ reject = rejected
nextStatus _ abstain = abstained
nextStatus _ qualify = qualified
nextStatus _ supersede = superseded
nextStatus _ requestEvidence = needsEvidence
nextStatus status openSource = status
nextStatus status followAuthority = status

openSourcePreservesReviewStatus :
  ∀ {status} →
  nextStatus status openSource ≡ status
openSourcePreservesReviewStatus = refl

followAuthorityPreservesReviewStatus :
  ∀ {status} →
  nextStatus status followAuthority ≡ status
followAuthorityPreservesReviewStatus = refl

data ReviewEffect : Set where
  statusChanged : ReviewStatus → ReviewEffect
  evidenceRequested : String → ReviewEffect
  sourceOpenRequested : ReviewEffect
  authorityFollowRequested : ReviewEffect

effectFor : ReviewStatus → ReviewAction → String → ReviewEffect
effectFor status accept _ = statusChanged (nextStatus status accept)
effectFor status reject _ = statusChanged (nextStatus status reject)
effectFor status abstain _ = statusChanged (nextStatus status abstain)
effectFor status qualify _ = statusChanged (nextStatus status qualify)
effectFor status supersede _ = statusChanged (nextStatus status supersede)
effectFor status requestEvidence requestRef = evidenceRequested requestRef
effectFor status openSource _ = sourceOpenRequested
effectFor status followAuthority _ = authorityFollowRequested

record ReviewReceipt (item : ReviewItem) (action : ReviewAction) : Set where
  constructor review-receipt
  field
    commandRef : String
    reviewerRef : String
    effect : ReviewEffect
    resultingStatus : ReviewStatus
    resultingStatusMatches :
      resultingStatus ≡ nextStatus (ReviewItem.currentStatus item) action
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ReviewReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReviewAcceptanceCreatesTruth : Set where
data ReviewRejectionProvesNegation : Set where
data EvidenceRequestIsNegativeFinding : Set where
data OpenSourceMutatesReviewStatus : Set where
data FollowAuthorityMutatesReviewStatus : Set where
data ReviewReceiptCreatesApplicability : Set where
data ReviewReceiptCreatesSemanticAuthority : Set where

acceptanceDoesNotCreateTruth : ReviewAcceptanceCreatesTruth → ⊥
acceptanceDoesNotCreateTruth ()

rejectionDoesNotProveNegation : ReviewRejectionProvesNegation → ⊥
rejectionDoesNotProveNegation ()

evidenceRequestIsNotNegativeFinding : EvidenceRequestIsNegativeFinding → ⊥
evidenceRequestIsNotNegativeFinding ()

openSourceDoesNotMutateReviewStatus : OpenSourceMutatesReviewStatus → ⊥
openSourceDoesNotMutateReviewStatus ()

followAuthorityDoesNotMutateReviewStatus : FollowAuthorityMutatesReviewStatus → ⊥
followAuthorityDoesNotMutateReviewStatus ()

reviewReceiptDoesNotCreateApplicability :
  ReviewReceiptCreatesApplicability → ⊥
reviewReceiptDoesNotCreateApplicability ()

reviewReceiptDoesNotCreateSemanticAuthority :
  ReviewReceiptCreatesSemanticAuthority → ⊥
reviewReceiptDoesNotCreateSemanticAuthority ()

record S29ReviewBoundary : Set where
  constructor s29-review-boundary
  field
    portableAcrossReviewKinds : Bool
    evidenceRequestSeparateFromRejection : Bool
    navigationPreservesReviewStatus : Bool
    reviewCreatesSemanticAuthority : Bool
    reviewCreatesApplicability : Bool
    reviewCreatesClaimTruth : Bool

canonicalS29ReviewBoundary : S29ReviewBoundary
canonicalS29ReviewBoundary =
  s29-review-boundary true true true false false false
