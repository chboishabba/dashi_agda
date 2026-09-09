module DASHI.Law.SensibLawCitationReviewUnitDecisionGateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rust parity for the citation-review-unit quotient and explicit review gate.
--
-- Observed runtime state before this source-written gate:
--   23 shortlisted occurrences -> 20 review units
--   Robinson: 6 occurrences -> 4 units
--   Modbury:   3 occurrences -> 2 units
--   network = 0
--   no treatment / authority / payment / closure was created.
--
-- The new Rust gate preserves every occurrence locator in a reviewed-unit
-- receipt while selecting one exact body anchor as the proposition pinpoint for
-- the existing PropositionReasoningEdge.  This is plumbing only: no real
-- Robinson/Modbury semantic review decision is asserted here.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

observedReviewUnitHead : String
observedReviewUnitHead = "8f8efafadea86f0b56246917e89c8b916deb5289"

reviewUnitDecisionGateSourceHead : String
reviewUnitDecisionGateSourceHead = "17dcf879996c976c93b095847cd4e354d4415b95"

record CitationReviewUnitDecisionBoundary : Set where
  constructor citationReviewUnitDecisionBoundary
  field
    shortlistOccurrenceCount : Nat
    shortlistOccurrenceCountIs23 : shortlistOccurrenceCount ≡ 23

    reviewUnitCount : Nat
    reviewUnitCountIs20 : reviewUnitCount ≡ 20

    robinsonOccurrenceCount : Nat
    robinsonOccurrenceCountIs6 : robinsonOccurrenceCount ≡ 6

    robinsonReviewUnitCount : Nat
    robinsonReviewUnitCountIs4 : robinsonReviewUnitCount ≡ 4

    modburyOccurrenceCount : Nat
    modburyOccurrenceCountIs3 : modburyOccurrenceCount ≡ 3

    modburyReviewUnitCount : Nat
    modburyReviewUnitCountIs2 : modburyReviewUnitCount ≡ 2

    reviewUnitPreservesAllOccurrenceLocators : Bool
    reviewUnitPreservesAllOccurrenceLocatorsIsTrue :
      reviewUnitPreservesAllOccurrenceLocators ≡ true

    reviewedReceiptPreservesSourceRevision : Bool
    reviewedReceiptPreservesSourceRevisionIsTrue :
      reviewedReceiptPreservesSourceRevision ≡ true

    reviewedReceiptPreservesCanonicalTextDigest : Bool
    reviewedReceiptPreservesCanonicalTextDigestIsTrue :
      reviewedReceiptPreservesCanonicalTextDigest ≡ true

    reviewDecisionMustSelectOwnedBodyAnchor : Bool
    reviewDecisionMustSelectOwnedBodyAnchorIsTrue :
      reviewDecisionMustSelectOwnedBodyAnchor ≡ true

    reviewedUnitMayFeedReasoningDelta : Bool
    reviewedUnitMayFeedReasoningDeltaIsTrue :
      reviewedUnitMayFeedReasoningDelta ≡ true

    realCullenUnitDecisionObserved : Bool
    realCullenUnitDecisionObservedIsFalse : realCullenUnitDecisionObserved ≡ false

canonicalCitationReviewUnitDecisionBoundary : CitationReviewUnitDecisionBoundary
canonicalCitationReviewUnitDecisionBoundary =
  citationReviewUnitDecisionBoundary
    23 refl
    20 refl
    6 refl
    4 refl
    3 refl
    2 refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReviewUnitAutomaticallyTreatment : Set where
data ReviewUnitAutomaticallyAuthority : Set where
data ReviewedUnitAutomaticallyConsumerClosure : Set where
data OccurrenceQuotientAutomaticallySemanticPayment : Set where

reviewUnitDoesNotBecomeTreatment : ReviewUnitAutomaticallyTreatment → ⊥
reviewUnitDoesNotBecomeTreatment ()

reviewUnitDoesNotBecomeAuthority : ReviewUnitAutomaticallyAuthority → ⊥
reviewUnitDoesNotBecomeAuthority ()

reviewedUnitDoesNotCloseConsumer : ReviewedUnitAutomaticallyConsumerClosure → ⊥
reviewedUnitDoesNotCloseConsumer ()

occurrenceQuotientDoesNotBecomeSemanticPayment :
  OccurrenceQuotientAutomaticallySemanticPayment → ⊥
occurrenceQuotientDoesNotBecomeSemanticPayment ()
