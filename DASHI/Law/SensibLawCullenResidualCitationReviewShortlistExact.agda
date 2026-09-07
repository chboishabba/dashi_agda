module DASHI.Law.SensibLawCullenResidualCitationReviewShortlistExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Residual-indexed review shortlist after the anchored Cullen observer.
--
-- Observed Rust v0.3 at fc5aeec...:
--   202 body paragraphs
--   163 material footnotes
--   163 body -> footnote anchors
--   190 citation candidates
--   189 anchored footnote candidates
--   network = 0
--   authority = experimental_candidate_only
--
-- The next Rust layer does not infer legal treatment.  The application supplies
-- criteria indexed by the exact live residual/proposition, and the runtime merely
-- selects unreviewed citation occurrences whose preserved body-anchor text
-- matches those criteria.  This is a review-work reduction, not proof payment.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

observedAnchoredQueueHead : String
observedAnchoredQueueHead = "fc5aeec3607fb908259d2d890f48435987c87320"

shortlistSourceHeadBeforeLocalValidation : String
shortlistSourceHeadBeforeLocalValidation =
  "cd3697c807f07ceb484215d19c90594f96655a35"

anchoredQueueSchema : String
anchoredQueueSchema = "sl.judgment_citation_review_queue.v0_3"

shortlistSchema : String
shortlistSchema = "sl.residual_citation_review_shortlist.v0_1"

liveResidualRef : String
liveResidualRef = "residual:cullen-positive-operational-act"

livePropositionRef : String
livePropositionRef = "prop:cullen-positive-operational-duty"

robinsonCitation : String
robinsonCitation = "[2018] AC 736"

modburyCitation : String
modburyCitation = "(2000) 205 CLR 254"

record CullenResidualCitationReviewShortlistBoundary : Set where
  constructor cullenResidualCitationReviewShortlistBoundary
  field
    anchoredQueueRuntimeObserved : Bool
    anchoredQueueRuntimeObservedIsTrue : anchoredQueueRuntimeObserved ≡ true

    bodyParagraphCount : Nat
    bodyParagraphCountIs202 : bodyParagraphCount ≡ 202

    materialFootnoteCount : Nat
    materialFootnoteCountIs163 : materialFootnoteCount ≡ 163

    footnoteAnchorCount : Nat
    footnoteAnchorCountIs163 : footnoteAnchorCount ≡ 163

    citationCandidateCount : Nat
    citationCandidateCountIs190 : citationCandidateCount ≡ 190

    anchoredFootnoteCandidateCount : Nat
    anchoredFootnoteCandidateCountIs189 : anchoredFootnoteCandidateCount ≡ 189

    anchoredQueueNetworkRequests : Nat
    anchoredQueueNetworkRequestsIsZero : anchoredQueueNetworkRequests ≡ 0

    shortlistCriteriaResidualIndexed : Bool
    shortlistCriteriaResidualIndexedIsTrue : shortlistCriteriaResidualIndexed ≡ true

    shortlistCriteriaPropositionIndexed : Bool
    shortlistCriteriaPropositionIndexedIsTrue : shortlistCriteriaPropositionIndexed ≡ true

    shortlistPreservesCandidateLocator : Bool
    shortlistPreservesCandidateLocatorIsTrue : shortlistPreservesCandidateLocator ≡ true

    shortlistPreservesAnchorLocatorAndText : Bool
    shortlistPreservesAnchorLocatorAndTextIsTrue :
      shortlistPreservesAnchorLocatorAndText ≡ true

    shortlistNetworkFreeByConstruction : Bool
    shortlistNetworkFreeByConstructionIsTrue :
      shortlistNetworkFreeByConstruction ≡ true

    shortlistRuntimeObserved : Bool
    shortlistRuntimeObservedIsFalse : shortlistRuntimeObserved ≡ false

    shortlistAutomaticallySemanticPayment : Bool
    shortlistAutomaticallySemanticPaymentIsFalse :
      shortlistAutomaticallySemanticPayment ≡ false

    shortlistAutomaticallyCitationTreatment : Bool
    shortlistAutomaticallyCitationTreatmentIsFalse :
      shortlistAutomaticallyCitationTreatment ≡ false

    shortlistAutomaticallyCurrentAuthority : Bool
    shortlistAutomaticallyCurrentAuthorityIsFalse :
      shortlistAutomaticallyCurrentAuthority ≡ false

    shortlistAutomaticallyConsumerClosure : Bool
    shortlistAutomaticallyConsumerClosureIsFalse :
      shortlistAutomaticallyConsumerClosure ≡ false

canonicalCullenResidualCitationReviewShortlistBoundary :
  CullenResidualCitationReviewShortlistBoundary
canonicalCullenResidualCitationReviewShortlistBoundary =
  cullenResidualCitationReviewShortlistBoundary
    true refl
    202 refl
    163 refl
    163 refl
    190 refl
    189 refl
    0 refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ShortlistMembershipAutomaticallySupport : Set where
data AnchorPhraseAutomaticallyTreatment : Set where
data ReviewPriorityAutomaticallyAuthority : Set where
data FewerCandidatesAutomaticallyClosure : Set where

shortlistMembershipDoesNotBecomeSupport :
  ShortlistMembershipAutomaticallySupport → ⊥
shortlistMembershipDoesNotBecomeSupport ()

anchorPhraseDoesNotBecomeTreatment : AnchorPhraseAutomaticallyTreatment → ⊥
anchorPhraseDoesNotBecomeTreatment ()

reviewPriorityDoesNotBecomeAuthority : ReviewPriorityAutomaticallyAuthority → ⊥
reviewPriorityDoesNotBecomeAuthority ()

fewerCandidatesDoNotCloseConsumer : FewerCandidatesAutomaticallyClosure → ⊥
fewerCandidatesDoNotCloseConsumer ()
