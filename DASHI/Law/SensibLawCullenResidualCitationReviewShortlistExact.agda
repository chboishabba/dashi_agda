module DASHI.Law.SensibLawCullenResidualCitationReviewShortlistExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Residual-indexed review shortlist after the anchored Cullen observer.
--
-- Observed anchored queue at fc5aeec...:
--   202 body paragraphs
--   163 material footnotes
--   163 body -> footnote anchors
--   190 citation candidates
--   189 anchored footnote candidates
--   network = 0
--
-- Observed shortlist at c8d4b37...:
--   190 input candidates -> 23 shortlist candidates
--   Robinson [2018] AC 736 = 6 shortlisted occurrences
--   Modbury (2000) 205 CLR 254 = 3 shortlisted occurrences
--   Mallonland (2024) 98 ALJR 956 = 0 shortlisted occurrences
--   network = 0
--   authority = experimental_candidate_only
--
-- A later Rust-only refactor removes PR13 Python orchestration/validation from
-- this lane.  That current source state is represented separately and is not
-- promoted to local-validation status merely because the earlier shortlist run
-- was validated.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

observedAnchoredQueueHead : String
observedAnchoredQueueHead = "fc5aeec3607fb908259d2d890f48435987c87320"

validatedShortlistHead : String
validatedShortlistHead = "c8d4b37034a62a9baaba09929dcee67922a31a8b"

currentRustOnlyRefactorSourceHead : String
currentRustOnlyRefactorSourceHead = "b88e3f6c4f9a649899152a66257e9b635508e6f4"

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

mallonlandCitation : String
mallonlandCitation = "(2024) 98 ALJR 956"

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
    shortlistRuntimeObservedIsTrue : shortlistRuntimeObserved ≡ true

    shortlistInputCandidateCount : Nat
    shortlistInputCandidateCountIs190 : shortlistInputCandidateCount ≡ 190

    shortlistCandidateCount : Nat
    shortlistCandidateCountIs23 : shortlistCandidateCount ≡ 23

    robinsonShortlistedOccurrenceCount : Nat
    robinsonShortlistedOccurrenceCountIs6 :
      robinsonShortlistedOccurrenceCount ≡ 6

    modburyShortlistedOccurrenceCount : Nat
    modburyShortlistedOccurrenceCountIs3 :
      modburyShortlistedOccurrenceCount ≡ 3

    mallonlandShortlistedOccurrenceCount : Nat
    mallonlandShortlistedOccurrenceCountIsZero :
      mallonlandShortlistedOccurrenceCount ≡ 0

    shortlistObservedNetworkRequests : Nat
    shortlistObservedNetworkRequestsIsZero : shortlistObservedNetworkRequests ≡ 0

    shortlistObservedCandidateOnly : Bool
    shortlistObservedCandidateOnlyIsTrue : shortlistObservedCandidateOnly ≡ true

    currentRustOnlyRefactorSourceWritten : Bool
    currentRustOnlyRefactorSourceWrittenIsTrue :
      currentRustOnlyRefactorSourceWritten ≡ true

    currentRustOnlyRefactorLocallyValidated : Bool
    currentRustOnlyRefactorLocallyValidatedIsFalse :
      currentRustOnlyRefactorLocallyValidated ≡ false

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
    true refl
    190 refl
    23 refl
    6 refl
    3 refl
    0 refl
    0 refl
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
data RustOnlyRefactorAutomaticallyValidated : Set where

shortlistMembershipDoesNotBecomeSupport :
  ShortlistMembershipAutomaticallySupport → ⊥
shortlistMembershipDoesNotBecomeSupport ()

anchorPhraseDoesNotBecomeTreatment : AnchorPhraseAutomaticallyTreatment → ⊥
anchorPhraseDoesNotBecomeTreatment ()

reviewPriorityDoesNotBecomeAuthority : ReviewPriorityAutomaticallyAuthority → ⊥
reviewPriorityDoesNotBecomeAuthority ()

fewerCandidatesDoNotCloseConsumer : FewerCandidatesAutomaticallyClosure → ⊥
fewerCandidatesDoNotCloseConsumer ()

rustOnlyRefactorDoesNotManufactureValidation :
  RustOnlyRefactorAutomaticallyValidated → ⊥
rustOnlyRefactorDoesNotManufactureValidation ()
