module DASHI.Law.SensibLawJudgmentFootnoteObserverRefinementExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Introspective observer refinement for the retained Cullen judgment.
--
-- v0.1 was observed inadequate: body-only canonical text produced one
-- self-citation candidate.  v0.2 is now locally observed on the retained
-- official DOCX at Rust head 00bb995...: 163 material footnotes, 190 citation
-- candidates, 189 footnote candidates, zero network, candidate-only.  The
-- Mallonland reporter identities are recovered at exact footnote locator 90.
--
-- This still does not establish treatment, proposition correspondence, ratio,
-- current authority or consumer closure.  The next introspective coordinate is
-- the body-paragraph <-> footnote-reference anchor needed to decide which of the
-- 190 candidates actually bears on a live residual.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustObservedRefinementHead : String
rustObservedRefinementHead = "00bb9957ace2d3c2ea7d6104ad5cab100dd29369"

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

missingCoordinateV01 : String
missingCoordinateV01 = "DOCX footnote bodies + reported/parallel citation forms"

nextMissingCoordinate : String
nextMissingCoordinate = "body paragraph <-> DOCX footnoteReference anchor"

mallonlandReportedCitation : String
mallonlandReportedCitation = "(2024) 98 ALJR 956"

mallonlandParallelCitation : String
mallonlandParallelCitation = "418 ALR 639"

mallonlandLocator : String
mallonlandLocator = "document:hca:[2026]-HCA-19:docx#footnote-90"

record JudgmentFootnoteObserverRefinementBoundary : Set where
  constructor judgmentFootnoteObserverRefinementBoundary
  field
    oldQueueNetworkRequests : Nat
    oldQueueNetworkRequestsIsZero : oldQueueNetworkRequests ≡ 0

    oldQueueCandidateCount : Nat
    oldQueueCandidateCountIsOne : oldQueueCandidateCount ≡ 1

    refinedQueueNetworkRequests : Nat
    refinedQueueNetworkRequestsIsZero : refinedQueueNetworkRequests ≡ 0

    refinedQueueFootnoteCount : Nat
    refinedQueueFootnoteCountIs163 : refinedQueueFootnoteCount ≡ 163

    refinedQueueCandidateCount : Nat
    refinedQueueCandidateCountIs190 : refinedQueueCandidateCount ≡ 190

    refinedQueueFootnoteCandidateCount : Nat
    refinedQueueFootnoteCandidateCountIs189 : refinedQueueFootnoteCandidateCount ≡ 189

    refinedQueueRuntimeObserved : Bool
    refinedQueueRuntimeObservedIsTrue : refinedQueueRuntimeObserved ≡ true

    refinedQueueCandidateOnly : Bool
    refinedQueueCandidateOnlyIsTrue : refinedQueueCandidateOnly ≡ true

    refinedObserverPreservesBody : Bool
    refinedObserverPreservesBodyIsTrue : refinedObserverPreservesBody ≡ true

    refinedObserverPreservesFootnoteIds : Bool
    refinedObserverPreservesFootnoteIdsIsTrue :
      refinedObserverPreservesFootnoteIds ≡ true

    mediumNeutralCitationExtractionRetained : Bool
    mediumNeutralCitationExtractionRetainedIsTrue :
      mediumNeutralCitationExtractionRetained ≡ true

    reportedCitationExtractionAdded : Bool
    reportedCitationExtractionAddedIsTrue : reportedCitationExtractionAdded ≡ true

    parallelReporterExtractionAdded : Bool
    parallelReporterExtractionAddedIsTrue : parallelReporterExtractionAdded ≡ true

    mallonlandReportedCitationObserved : Bool
    mallonlandReportedCitationObservedIsTrue :
      mallonlandReportedCitationObserved ≡ true

    mallonlandParallelCitationObserved : Bool
    mallonlandParallelCitationObservedIsTrue :
      mallonlandParallelCitationObserved ≡ true

    mallonlandFootnoteLocatorObserved : Bool
    mallonlandFootnoteLocatorObservedIsTrue :
      mallonlandFootnoteLocatorObserved ≡ true

    bodyFootnoteAnchorPreserved : Bool
    bodyFootnoteAnchorPreservedIsFalse : bodyFootnoteAnchorPreserved ≡ false

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
    0 refl
    163 refl
    190 refl
    189 refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
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
data FootnoteIdentityAutomaticallyResidualRelevance : Set where

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

footnoteIdentityDoesNotBecomeResidualRelevance :
  FootnoteIdentityAutomaticallyResidualRelevance → ⊥
footnoteIdentityDoesNotBecomeResidualRelevance ()
