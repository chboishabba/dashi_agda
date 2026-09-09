module DASHI.Law.SensibLawOfflineResearchEngineCurrentParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawOfflineResearchEngineRoadmapEverything as Roadmap
import DASHI.Law.SensibLawOfficialHCAFullJudgmentLiveReceipt516867cExact as FullJudgment
import DASHI.Law.SensibLawJudgmentFootnoteObserverRefinementExact as FootnoteRefinement
import DASHI.Law.SensibLawJudgmentFootnoteAnchorObserverRefinementExact as AnchorRefinement

------------------------------------------------------------------------
-- Current parity overlay.
--
-- Current observed state:
--   * full official HCA DOCX acquisition/materialization is observed;
--   * exact carrier and body-only text digests are pinned;
--   * body-only v0.1 citation observation was inadequate (1 candidate);
--   * body+footnote v0.2 is observed at Rust head 00bb995... with 163
--     footnotes, 190 candidates and 189 footnote candidates, network=0;
--   * Mallonland reporter identities are recovered at footnote 90;
--   * v0.3 body-paragraph <-> footnoteReference anchor preservation is source
--     implemented but not yet runtime-observed;
--   * extraction/anchors remain candidate observations, not treatment/payment;
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

    bodyFootnoteCitationQueueV02Observed : Bool
    bodyFootnoteCitationQueueV02ObservedIsTrue :
      bodyFootnoteCitationQueueV02Observed ≡ true

    mallonlandReporterIdentityRecovered : Bool
    mallonlandReporterIdentityRecoveredIsTrue :
      mallonlandReporterIdentityRecovered ≡ true

    bodyFootnoteAnchorV03Implemented : Bool
    bodyFootnoteAnchorV03ImplementedIsTrue :
      bodyFootnoteAnchorV03Implemented ≡ true

    bodyFootnoteAnchorV03RuntimeObserved : Bool
    bodyFootnoteAnchorV03RuntimeObservedIsFalse :
      bodyFootnoteAnchorV03RuntimeObserved ≡ false

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

selectedAnchorRefinementBoundary :
  AnchorRefinement.FootnoteAnchorObserverRefinementBoundary
selectedAnchorRefinementBoundary =
  AnchorRefinement.canonicalFootnoteAnchorObserverRefinementBoundary

------------------------------------------------------------------------
-- Current-parity firewalls.
------------------------------------------------------------------------

data RuntimeObservationAutomaticallyKernelProof : Set where
data ObserverRefinementAutomaticallyReviewedTreatment : Set where
data AnchorObservationAutomaticallyResidualPayment : Set where

runtimeObservationDoesNotBecomeKernelProof :
  RuntimeObservationAutomaticallyKernelProof → ⊥
runtimeObservationDoesNotBecomeKernelProof ()

observerRefinementDoesNotBecomeReviewedTreatment :
  ObserverRefinementAutomaticallyReviewedTreatment → ⊥
observerRefinementDoesNotBecomeReviewedTreatment ()

anchorObservationDoesNotBecomeResidualPayment :
  AnchorObservationAutomaticallyResidualPayment → ⊥
anchorObservationDoesNotBecomeResidualPayment ()
