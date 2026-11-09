module DASHI.Law.SensibLawWoogarooSection135AReportAccess20261109Exact where

-- EPBC 2019/8575, 9 November 2026.
--
-- NEW PRIMARY-LAW ACCESS CUT, NOT A RECEIVED REPORT OR LEGAL FINDING:
-- Original EPBC Act 1999 compilation 1 July 2026 s135A(1)(b),
-- (2)-(5) expressly provides for a person to request a copy of the
-- s95C recommendation report after the Part9 decision, subject to
-- charging and statutory redaction/refusal grounds.
-- Signed Part9 approval EPBC 2019/8575 is dated 16 October 2026.
--
-- The Environment Protection Reform Act 2025 Sch1 items 232-234
-- later substitutes website publication of recommendations. Sch1
-- item689 says which recommendation reports the amendments apply to
-- *once they commence*. It does NOT specify a commencement day.
-- Exact commencement for items232-234 (and any relevant savings)
-- remains a separate source obligation; do not silently assume it
-- was 24 August, 16 October, or 1 December 2026.
--
-- Existing original applicable-law matrix remains the owner:
-- DASHI/Law/SensibLawWoogarooEPBC20198575ApplicableLawMatrixExact.
-- Actual reporting/ministerial receipt, proposed decision evidence,
-- full 95B comments, and actual report delivery are all UNRECEIVED.
-- No request, FOI, filing or regulatory allegation has been sent.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Law.SensibLawWoogarooEPBC20198575ApplicableLawMatrixExact as Law
import DASHI.Law.SensibLawWoogarooOperativeInstrumentEvidenceCut20261109Exact as Approval

data AccessRoute : Set where
  statutoryRequestUnder135A
    laterMandatoryWebsitePublication
    freedomOfInformationForOtherRecords : AccessRoute

record OriginalAccessGate : Set where
  constructor original-access-gate
  field
    approvalSignedYYYYMMDD : Nat
    decisionHasOccurred : Bool
    originalCompilationRequestRouteExists : Bool
    amendment232to234CommencementVerified : Bool
    recommendationReportActuallyReceived : Bool
    publicReportPDFAuthenticated : Bool
    agencyAccessRequestSent : Bool
    freedomOfInformationRequestSent : Bool
open OriginalAccessGate public

reportedState : OriginalAccessGate
reportedState = original-access-gate
  20261016 true true false false false false false

directRequestRouteHistoricallyAvailable :
  originalCompilationRequestRouteExists reportedState ≡ true
directRequestRouteHistoricallyAvailable = refl

no135AReportReceived :
  recommendationReportActuallyReceived reportedState ≡ false
no135AReportReceived = refl

noAgencyRequestSent :
  agencyAccessRequestSent reportedState ≡ false
noAgencyRequestSent = refl

newPublicationCommencementNotVerified :
  amendment232to234CommencementVerified reportedState ≡ false
newPublicationCommencementNotVerified = refl

-- This cross-check is a REUSE of the original legal matrix's
-- source-typed report-access and transitional-date interfaces,
-- not a declaration that an amending law commenced in October.
priorApplicableLaw135A : Law.ApplicableRule
priorApplicableLaw135A = Law.section135APublication

originalJulyRequestText : Law.ApplicableRule
originalJulyRequestText = Law.section135APreDecisionOnRequest

s95CStillUnreceived :
  Approval.mandatoryOriginalDecisionStages
    Approval.original95CSecretaryRecommendation ≡
      Approval.unknownOriginal
s95CStillUnreceived = refl
