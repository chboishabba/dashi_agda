module DASHI.Law.SensibLawJudgmentFootnoteObserverRefinementExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Introspective observer refinement for the retained Cullen judgment.
--
-- Observed v0.1 queue:
--   body-only canonical observer -> one self-citation candidate.
--
-- Artifact inspection shows the exact missing carrier class: the DOCX contains
-- material footnote bodies in word/footnotes.xml, and those footnotes carry the
-- reporter identities needed by the citation/treatment consumer.  The Rust
-- repair preserves those footnotes by stable footnote id, adds reported/parallel
-- citation-shape extraction, and produces a distinct body+footnotes observer
-- digest.  The repaired v0.2 queue remains unobserved until local execution.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustRefinementSourceHead : String
rustRefinementSourceHead = "23e34f4f92e06e147369a6daddd15c658eb317d6"

oldQueueSchema : String
oldQueueSchema = "sl.judgment_citation_review_queue.v0_1"

refinedQueueSchema : String
refinedQueueSchema = "sl.judgment_citation_review_queue.v0_2"

sourceRevisionRef : String
sourceRevisionRef =
  "source-revision:sha256:f171fcaa304de4e1a8be9b7e2a200a181025a81456fa89dec18516805cad15b9"

bodyOnlyCanonicalTextDigest : String
bodyOnlyCanonicalTextDigest =
  "sha256:53f4037cbb6a254634b43e5747bf398f44519a8eea1c9a904d146f7674564b5a"

missingCoordinate : String
missingCoordinate = "DOCX footnote bodies + reported/parallel citation forms"

mallonlandReportedCitation : String
mallonlandReportedCitation = "(2024) 98 ALJR 956"

mallonlandParallelCitation : String
mallonlandParallelCitation = "418 ALR 639"

record JudgmentFootnoteObserverRefinementBoundary : Set where
  constructor judgmentFootnoteObserverRefinementBoundary
  field
    oldQueueNetworkRequests : Nat
    oldQueueNetworkRequestsIsZero : oldQueueNetworkRequests ≡ 0

    oldQueueCandidateCount : Nat
    oldQueueCandidateCountIsOne : oldQueueCandidateCount ≡ 1

    oldQueueAllCandidatesReviewed : Bool
    oldQueueAllCandidatesReviewedIsFalse : oldQueueAllCandidatesReviewed ≡ false

    oldQueueClaimedSemanticCorrespondence : Bool
    oldQueueClaimedSemanticCorrespondenceIsFalse :
      oldQueueClaimedSemanticCorrespondence ≡ false

    refinedObserverPreservesBody : Bool
    refinedObserverPreservesBodyIsTrue : refinedObserverPreservesBody ≡ true

    refinedObserverPreservesFootnoteIds : Bool
    refinedObserverPreservesFootnoteIdsIsTrue :
      refinedObserverPreservesFootnoteIds ≡ true

    refinedObserverUsesDistinctDigest : Bool
    refinedObserverUsesDistinctDigestIsTrue :
      refinedObserverUsesDistinctDigest ≡ true

    mediumNeutralCitationExtractionRetained : Bool
    mediumNeutralCitationExtractionRetainedIsTrue :
      mediumNeutralCitationExtractionRetained ≡ true

    reportedCitationExtractionAdded : Bool
    reportedCitationExtractionAddedIsTrue : reportedCitationExtractionAdded ≡ true

    parallelReporterExtractionAdded : Bool
    parallelReporterExtractionAddedIsTrue : parallelReporterExtractionAdded ≡ true

    footnoteCandidatesHaveStableLocators : Bool
    footnoteCandidatesHaveStableLocatorsIsTrue :
      footnoteCandidatesHaveStableLocators ≡ true

    mallonlandReporterCandidateRequiredByValidation : Bool
    mallonlandReporterCandidateRequiredByValidationIsTrue :
      mallonlandReporterCandidateRequiredByValidation ≡ true

    refinedQueueNetworkRequests : Nat
    refinedQueueNetworkRequestsIsZero : refinedQueueNetworkRequests ≡ 0

    refinedQueueRuntimeObserved : Bool
    refinedQueueRuntimeObservedIsFalse : refinedQueueRuntimeObserved ≡ false

    extractionAutomaticallyCitationTreatment : Bool
    extractionAutomaticallyCitationTreatmentIsFalse :
      extractionAutomaticallyCitationTreatment ≡ false

    extractionAutomaticallyCurrentAuthority : Bool
    extractionAutomaticallyCurrentAuthorityIsFalse :
      extractionAutomaticallyCurrentAuthority ≡ false

canonicalJudgmentFootnoteObserverRefinementBoundary :
  JudgmentFootnoteObserverRefinementBoundary
canonicalJudgmentFootnoteObserverRefinementBoundary =
  judgmentFootnoteObserverRefinementBoundary
    0 refl
    1 refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    0 refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls: recovered coordinates remain observations until reviewed.
------------------------------------------------------------------------

data FootnotePresenceAutomaticallyCitationTreatment : Set where
data ReporterShapeAutomaticallyAuthorityIdentity : Set where
data MoreCitationCandidatesAutomaticallyConsumerClosure : Set where
data ObserverRefinementAutomaticallyFormalProgress : Set where

footnotePresenceDoesNotBecomeCitationTreatment :
  FootnotePresenceAutomaticallyCitationTreatment → ⊥
footnotePresenceDoesNotBecomeCitationTreatment ()

reporterShapeDoesNotBecomeAuthorityIdentity :
  ReporterShapeAutomaticallyAuthorityIdentity → ⊥
reporterShapeDoesNotBecomeAuthorityIdentity ()

moreCitationCandidatesDoNotCloseConsumer :
  MoreCitationCandidatesAutomaticallyConsumerClosure → ⊥
moreCitationCandidatesDoNotCloseConsumer ()

observerRefinementDoesNotBecomeFormalProgress :
  ObserverRefinementAutomaticallyFormalProgress → ⊥
observerRefinementDoesNotBecomeFormalProgress ()
