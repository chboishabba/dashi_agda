module DASHI.Law.SensibLawLegalReasonablenessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ObserverSituatedReasonablenessExact as Situated

------------------------------------------------------------------------
-- SENSIBLAW LEGAL REASONABLENESS
--
-- Historical/source-bound legal adapter over the generic situated-observer
-- reasonableness core.  Citation records provenance only: it does not import
-- proof, legal authority, moral justification, or a case-specific conclusion.
------------------------------------------------------------------------

wednesburyJudgment : Source.AttributedSource
wednesburyJudgment = Source.mkNoDOISource
  "Court of Appeal of England and Wales"
  "Associated Provincial Picture Houses Ltd v Wednesbury Corporation [1947] EWCA Civ 1"
  "BAILII / Law Reports, [1948] 1 KB 223"
  "1947"
  "https://www.bailii.org/ew/cases/EWCA/1947/1.html"
  (Source.namedSourceKind "court judgment")
  "Primary published judgment manifestation for the Sunday-cinema licensing dispute, relevant/irrelevant consideration discussion, no-reasonable-authority formulation, and dismissal of the appeal. The judgment is a source for what the court held/stated, not a general moral or political authority."
  Source.publicAttribution

liJudgment : Source.AttributedSource
liJudgment = Source.mkNoDOISource
  "High Court of Australia"
  "Minister for Immigration and Citizenship v Li [2013] HCA 18"
  "High Court of Australia"
  "2013"
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/minister-immigration-and-citizenship-v-li"
  (Source.namedSourceKind "court judgment")
  "Primary High Court source for the legal-unreasonableness treatment of the Tribunal's refusal to adjourn, including statutory scope/purpose, the non-exhaustive status of Wednesbury, and evident/intelligible justification language."
  Source.publicAttribution

szvfwJudgment : Source.AttributedSource
szvfwJudgment = Source.mkNoDOISource
  "High Court of Australia"
  "Minister for Immigration and Border Protection v SZVFW [2018] HCA 30"
  "High Court of Australia"
  "2018"
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/minister-immigration-and-border-protection-v-szvfw"
  (Source.namedSourceKind "court judgment")
  "Primary High Court source for the later legal-unreasonableness application concerning the Tribunal proceeding without the respondents, including fact-dependence and merits-review separation."
  Source.publicAttribution

legalReasonablenessSources : List Source.AttributedSource
legalReasonablenessSources =
  wednesburyJudgment ∷ liJudgment ∷ szvfwJudgment ∷ []

legalReasonablenessSourceAtlas : Source.AttributedSourceAtlas
legalReasonablenessSourceAtlas = Source.mkSourceAtlas
  "Wednesbury / Australian legal reasonableness source atlas"
  "DASHI.Law.SensibLawLegalReasonablenessExact"
  legalReasonablenessSources
  "Source-bound doctrinal lineage only. Citation does not make one jurisdiction's formulation definitionally identical to another, import proof, or create legal/normative authority outside the literal source relation."

------------------------------------------------------------------------
-- Exact bounded case receipts.
------------------------------------------------------------------------

record WednesburyCaseReceipt : Set where
  constructor wednesburyCaseReceipt
  field
    wednesburySource : Source.AttributedSource
    childrenUnder15SundayCondition : Bool
    wednesburyAppealDismissed : Bool
    relevantIrrelevantConsiderationDiscussionLocated : Bool
    noReasonableAuthorityFormulationLocated : Bool

open WednesburyCaseReceipt public

canonicalWednesburyCaseReceipt : WednesburyCaseReceipt
canonicalWednesburyCaseReceipt =
  wednesburyCaseReceipt
    wednesburyJudgment
    true
    true
    true
    true

record LiCaseReceipt : Set where
  constructor liCaseReceipt
  field
    liSource : Source.AttributedSource
    tribunalAdjournmentRefusalInIssue : Bool
    liTribunalRefusalHeldLegallyUnreasonable : Bool
    wednesburyNotStartingOrEndPointLocated : Bool
    evidentIntelligibleJustificationLanguageLocated : Bool
    statutoryScopePurposeFrameworkLocated : Bool

open LiCaseReceipt public

canonicalLiCaseReceipt : LiCaseReceipt
canonicalLiCaseReceipt =
  liCaseReceipt
    liJudgment
    true
    true
    true
    true
    true

record SZVFWCaseReceipt : Set where
  constructor szvfwCaseReceipt
  field
    szvfwSource : Source.AttributedSource
    tribunalProceedWithoutRespondentsInIssue : Bool
    szvfwTribunalDecisionHeldLegallyUnreasonable : Bool
    factDependentLanguageLocated : Bool
    meritsReviewSeparationLocated : Bool

open SZVFWCaseReceipt public

canonicalSZVFWCaseReceipt : SZVFWCaseReceipt
canonicalSZVFWCaseReceipt =
  szvfwCaseReceipt
    szvfwJudgment
    true
    false
    true
    true

------------------------------------------------------------------------
-- Doctrine separation.
--
-- These Booleans are anti-collapse contracts.  They do not attempt to encode
-- every ground of Australian judicial review or every consequence of legal
-- unreasonableness.
------------------------------------------------------------------------

record LegalReasonablenessBoundary : Set where
  constructor legalReasonablenessBoundary
  field
    meritsDisagreementAutomaticallyLegalUnreasonableness : Bool
    factualErrorAutomaticallyLegalUnreasonableness : Bool
    relevantConsiderationsGroundDefinitionallyLegalUnreasonableness : Bool
    legalUnreasonablenessAutomaticallyJudicialMeritsSubstitution : Bool
    wednesburyFormulationDefinitionallyExhaustsAustralianLegalUnreasonableness : Bool
    harshDecisionAutomaticallyLegalUnreasonableness : Bool
    sourceCitationAutomaticallyCreatesLegalAuthority : Bool
    statutoryContextIndexesReasonablenessInquiry : Bool
    reasonsMayBeFocalPointWithoutBeingWholeInquiry : Bool

open LegalReasonablenessBoundary public

canonicalLegalReasonablenessBoundary : LegalReasonablenessBoundary
canonicalLegalReasonablenessBoundary =
  legalReasonablenessBoundary
    false
    false
    false
    false
    false
    false
    false
    true
    true

------------------------------------------------------------------------
-- Thin adapter receipt: the generic owner supplies the indexing/refinement
-- pattern, but generic reasonableness is not definitionally legal
-- reasonableness.
------------------------------------------------------------------------

record LegalReasonablenessAdapterReceipt : Set where
  constructor legalReasonablenessAdapterReceipt
  field
    situatedReasonablenessOwnerReferenced : Bool
    reasonablenessIndexIsReusable : Bool
    genericReasonablenessDefinitionallyLegalReasonableness : Bool

open LegalReasonablenessAdapterReceipt public

canonicalLegalReasonablenessAdapterReceipt : LegalReasonablenessAdapterReceipt
canonicalLegalReasonablenessAdapterReceipt =
  legalReasonablenessAdapterReceipt true true false

legalReasonablenessIndexExample : Situated.ReasonablenessIndex
legalReasonablenessIndexExample =
  Situated.reasonablenessIndex
    "reviewing court / statutory decision-maker"
    "particular statute and judicial-review source"
    "lawful range for the statutory power"
    "mandatory/relevant factors as fixed by the legal source"
    "legal unreasonableness threshold"
    "whether the purported exercise of power is legally unreasonable"
    "judicial review, not merits substitution"
