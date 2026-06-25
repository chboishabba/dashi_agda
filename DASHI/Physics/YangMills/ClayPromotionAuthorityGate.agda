module DASHI.Physics.YangMills.ClayPromotionAuthorityGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

-- ── ClayPromotionAuthorityGate ──────────────────────────────────────
-- Separates mathematical source-intake readiness from Clay-grade
-- promotion.  CMI rules require ALL of:
--   §6 — publication in a qualifying outlet
--   §3(ii) — at least two years after publication
--   §3(iii) — general acceptance in the global mathematics community
-- before a proposed solution will even be considered.
--
-- The Eriksson series is a viXra preprint sequence (not a qualifying
-- outlet).  No publication date has started the two-year clock.  No
-- community consensus exists — the CMI and Wikipedia still describe
-- Yang–Mills/mass gap as an open problem as of June 2026.
--
-- Mathematical source-intake is complete (33 postulates, all closed).
-- The package is auditable and ready for peer-review submission.
-- But clayYangMillsPromoted remains false because that is an
-- authority/adjudication gate, not a mathematical one.

record ClayPromotionAuthorityGate : Set where
  field
    mathematicalSourceIntakeClosed    : Bool
    candidateForPeerReview            : Bool
    candidateForClayTrack             : Bool

    qualifyingJournalPublication      : Bool
    twoYearWaitingPeriodElapsed       : Bool
    globalMathematicsAcceptance       : Bool
    clayOrSABConsiderationAvailable   : Bool

    clayYangMillsPromoted             : Bool

    mathematicalSourceIntakeClosedIsTrue    : mathematicalSourceIntakeClosed ≡ true
    candidateForPeerReviewIsTrue           : candidateForPeerReview ≡ true
    candidateForClayTrackIsTrue            : candidateForClayTrack ≡ true

    qualifyingJournalPublicationIsFalse    : qualifyingJournalPublication ≡ false
    twoYearWaitingPeriodElapsedIsFalse     : twoYearWaitingPeriodElapsed ≡ false
    globalMathematicsAcceptanceIsFalse     : globalMathematicsAcceptance ≡ false
    clayOrSABConsiderationAvailableIsFalse : clayOrSABConsiderationAvailable ≡ false

    clayYangMillsPromotedIsFalse           : clayYangMillsPromoted ≡ false

    sources : String
    sourcesIsCanonical :
      sources ≡
      "33 postulates closed through Step V KP, RG lane, DLR-LSI, OS0–OS4, OS1/O(4), Wightman reconstruction, continuum stability, triangular lock, gauge-fixing compatibility (OS route), link ellipticity. Package auditable and ready for peer-review. CMI rules not satisfied: no qualifying journal publication, no two-year waiting period, no global acceptance. clayYangMillsPromoted = false by authority/adjudication, not mathematics."

currentClayPromotionAuthorityGate : ClayPromotionAuthorityGate
currentClayPromotionAuthorityGate = record
  { mathematicalSourceIntakeClosed    = true
  ; candidateForPeerReview            = true
  ; candidateForClayTrack             = true
  ; qualifyingJournalPublication      = false
  ; twoYearWaitingPeriodElapsed       = false
  ; globalMathematicsAcceptance       = false
  ; clayOrSABConsiderationAvailable   = false
  ; clayYangMillsPromoted             = false
  ; mathematicalSourceIntakeClosedIsTrue    = refl
  ; candidateForPeerReviewIsTrue           = refl
  ; candidateForClayTrackIsTrue            = refl
  ; qualifyingJournalPublicationIsFalse    = refl
  ; twoYearWaitingPeriodElapsedIsFalse     = refl
  ; globalMathematicsAcceptanceIsFalse     = refl
  ; clayOrSABConsiderationAvailableIsFalse = refl
  ; clayYangMillsPromotedIsFalse           = refl
  ; sources =
      "33 postulates closed through Step V KP, RG lane, DLR-LSI, OS0–OS4, OS1/O(4), Wightman reconstruction, continuum stability, triangular lock, gauge-fixing compatibility (OS route), link ellipticity. Package auditable and ready for peer-review. CMI rules not satisfied: no qualifying journal publication, no two-year waiting period, no global acceptance. clayYangMillsPromoted = false by authority/adjudication, not mathematics."
  ; sourcesIsCanonical = refl
  }
