module DASHI.Law.SensibLawOfflineResearchEngineCurrentParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawOfflineResearchEngineRoadmapEverything as Roadmap
import DASHI.Law.SensibLawOfficialHCAFullJudgmentLiveReceipt516867cExact as FullJudgment
import DASHI.Law.SensibLawJudgmentFootnoteObserverRefinementExact as FootnoteRefinement

------------------------------------------------------------------------
-- Current parity overlay.
--
-- The older roadmap capstone remains the historical aggregate for the offline
-- and initial governed-online implementation.  This overlay owns the newer live
-- facts without rewriting history:
--   * full official HCA DOCX acquisition/materialization is observed;
--   * both carrier and body-only canonical-text digests are pinned exactly;
--   * the first body-only citation queue observed only one self citation;
--   * the Rust observer refinement now preserves DOCX footnotes and reported /
--     parallel citation forms;
--   * the refined v0.2 queue is not yet runtime-observed;
--   * local Rust validation is not Agda kernel certification.
------------------------------------------------------------------------

record CurrentResearchEngineParityBoundary : Set where
  constructor currentResearchEngineParityBoundary
  field
    historicalRoadmapRetained : Bool
    historicalRoadmapRetainedIsTrue : historicalRoadmapRetained ≡ true

    fullOfficialJudgmentObserved : Bool
    fullOfficialJudgmentObservedIsTrue : fullOfficialJudgmentObserved ≡ true

    fullOfficialJudgmentExactCarrierDigestPinned : Bool
    fullOfficialJudgmentExactCarrierDigestPinnedIsTrue :
      fullOfficialJudgmentExactCarrierDigestPinned ≡ true

    fullOfficialJudgmentExactBodyTextDigestPinned : Bool
    fullOfficialJudgmentExactBodyTextDigestPinnedIsTrue :
      fullOfficialJudgmentExactBodyTextDigestPinned ≡ true

    bodyOnlyCitationObserverInadequacyObserved : Bool
    bodyOnlyCitationObserverInadequacyObservedIsTrue :
      bodyOnlyCitationObserverInadequacyObserved ≡ true

    footnoteObserverRefinementImplemented : Bool
    footnoteObserverRefinementImplementedIsTrue :
      footnoteObserverRefinementImplemented ≡ true

    reportedCitationRefinementImplemented : Bool
    reportedCitationRefinementImplementedIsTrue :
      reportedCitationRefinementImplemented ≡ true

    refinedCitationQueueRuntimeObserved : Bool
    refinedCitationQueueRuntimeObservedIsFalse :
      refinedCitationQueueRuntimeObserved ≡ false

    exactCurrentRustHeadLiveExecutionObserved : Bool
    exactCurrentRustHeadLiveExecutionObservedIsFalse :
      exactCurrentRustHeadLiveExecutionObserved ≡ false

    agdaKernelCertificationObserved : Bool
    agdaKernelCertificationObservedIsFalse : agdaKernelCertificationObserved ≡ false

canonicalCurrentResearchEngineParityBoundary : CurrentResearchEngineParityBoundary
canonicalCurrentResearchEngineParityBoundary =
  currentResearchEngineParityBoundary
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

selectedHistoricalRoadmapBoundary : Roadmap.OfflineResearchEngineBoundary
selectedHistoricalRoadmapBoundary = Roadmap.canonicalOfflineResearchEngineBoundary

selectedFullJudgmentReceipt : FullJudgment.ObservedFullJudgmentLiveReceipt
selectedFullJudgmentReceipt = FullJudgment.canonicalObservedFullJudgmentLiveReceipt

selectedFootnoteRefinementBoundary :
  FootnoteRefinement.JudgmentFootnoteObserverRefinementBoundary
selectedFootnoteRefinementBoundary =
  FootnoteRefinement.canonicalJudgmentFootnoteObserverRefinementBoundary

------------------------------------------------------------------------
-- Current-parity firewalls.
------------------------------------------------------------------------

data RuntimeObservationAutomaticallyKernelProof : Set where
data ObserverRefinementAutomaticallyReviewedTreatment : Set where

runtimeObservationDoesNotBecomeKernelProof :
  RuntimeObservationAutomaticallyKernelProof → ⊥
runtimeObservationDoesNotBecomeKernelProof ()

observerRefinementDoesNotBecomeReviewedTreatment :
  ObserverRefinementAutomaticallyReviewedTreatment → ⊥
observerRefinementDoesNotBecomeReviewedTreatment ()
