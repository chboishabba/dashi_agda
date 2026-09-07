module DASHI.Law.QueenslandButForSourceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- QUEENSLAND FACTUAL CAUSATION SOURCE / ATTRIBUTION BOUNDARY
--
-- Attribution policy:
--   * Queensland legislation owns Queensland statutory propositions.
--   * High Court cases below are calibrations concerning the materially similar
--     NSW Civil Liability Act 2002 s 5D architecture; they are not represented
--     as the textual source of Queensland Civil Liability Act 2003 s 11.
--   * DASHI owns the typed records, counterfactual fibres, compilers and
--     non-promotion firewalls built around those source propositions.
------------------------------------------------------------------------

data SourceRole : Set where
  primaryQueenslandLegislation
  highCourtCalibration
  dashiOriginalAbstraction
  : SourceRole

record LegalSourceAttribution : Set where
  constructor legalSourceAttribution
  field
    role : SourceRole
    title : String
    citation : String
    sourceURL : String
    propositionBoundary : String

open LegalSourceAttribution public

queenslandCivilLiabilityAct : LegalSourceAttribution
queenslandCivilLiabilityAct = legalSourceAttribution
  primaryQueenslandLegislation
  "Civil Liability Act 2003 (Qld), ss 10-12"
  "Civil Liability Act 2003 (Qld) ss 10, 11, 12"
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-2003-016"
  "Primary source for Queensland statutory necessary-condition factual causation, distinct scope of liability, exceptional-case route, subjective claimant counterfactual rule, and causation onus/balance-of-probabilities rule."

strongCalibration : LegalSourceAttribution
strongCalibration = legalSourceAttribution
  highCourtCalibration
  "Strong v Woolworths Limited"
  "[2012] HCA 5"
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/strong-v-woolworths-limited"
  "High Court calibration concerning factual causation, necessary condition and evidentiary inference under NSW Civil Liability Act 2002 s 5D; not the textual source of Queensland s 11."

wallaceCalibration : LegalSourceAttribution
wallaceCalibration = legalSourceAttribution
  highCourtCalibration
  "Wallace v Kam"
  "[2013] HCA 19"
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/wallace-v-kam"
  "High Court calibration separating factual causation from scope of liability under NSW Civil Liability Act 2002 s 5D; not the textual source of Queensland s 11."

dashiButForArchitecture : LegalSourceAttribution
dashiButForArchitecture = legalSourceAttribution
  dashiOriginalAbstraction
  "DASHI legal but-for causation architecture"
  "DASHI-original"
  "DASHI/Law/LegalFactualCausationButForExact.agda"
  "Typed breach-correction intervention, counterfactual fibre, robust/selected/underidentified counterfactual distinctions, parser bridge and compiler boundaries are DASHI abstractions, not language attributed to the legislature or High Court."

------------------------------------------------------------------------
-- Source-backed Queensland proposition coordinates.
------------------------------------------------------------------------

record QueenslandCausationStatutoryCoordinates : Set where
  constructor queenslandCausationStatutoryCoordinates
  field
    factualCausationRequiresNecessaryConditionOrdinarily : Bool
    factualCausationRequiresNecessaryConditionOrdinarilyIsTrue :
      factualCausationRequiresNecessaryConditionOrdinarily ≡ true

    scopeOfLiabilityIsSeparateElement : Bool
    scopeOfLiabilityIsSeparateElementIsTrue :
      scopeOfLiabilityIsSeparateElement ≡ true

    exceptionalCaseRouteExists : Bool
    exceptionalCaseRouteExistsIsTrue : exceptionalCaseRouteExists ≡ true

    claimantCounterfactualMayRequireSubjectiveInquiry : Bool
    claimantCounterfactualMayRequireSubjectiveInquiryIsTrue :
      claimantCounterfactualMayRequireSubjectiveInquiry ≡ true

    causationFactsUseBalanceOfProbabilities : Bool
    causationFactsUseBalanceOfProbabilitiesIsTrue :
      causationFactsUseBalanceOfProbabilities ≡ true

    avoidabilityAloneEstablishesLiability : Bool
    avoidabilityAloneEstablishesLiabilityIsFalse :
      avoidabilityAloneEstablishesLiability ≡ false

    primarySource : LegalSourceAttribution

canonicalQueenslandCausationCoordinates : QueenslandCausationStatutoryCoordinates
canonicalQueenslandCausationCoordinates =
  queenslandCausationStatutoryCoordinates
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    queenslandCivilLiabilityAct

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data HighCourtNSWCaseIsTextualSourceOfQueenslandSection11 : Set where
data DASHICompilerIsLegislativeText : Set where
data ParserOutputIsLegalSourceAuthority : Set where
data SourceBackedPropositionTransfersAllDASHIAbstractionsToSource : Set where

highCourtCalibrationIsNotQueenslandTextualSource :
  HighCourtNSWCaseIsTextualSourceOfQueenslandSection11 → ⊥
highCourtCalibrationIsNotQueenslandTextualSource ()

dashiCompilerIsNotLegislativeText : DASHICompilerIsLegislativeText → ⊥
dashiCompilerIsNotLegislativeText ()

parserOutputIsNotLegalSourceAuthority : ParserOutputIsLegalSourceAuthority → ⊥
parserOutputIsNotLegalSourceAuthority ()

sourcePropositionDoesNotOwnDashiAbstraction :
  SourceBackedPropositionTransfersAllDASHIAbstractionsToSource → ⊥
sourcePropositionDoesNotOwnDashiAbstraction ()

record AttributionBoundary : Set where
  constructor attributionBoundary
  field
    primaryLawOwnsStatutoryProposition : Bool
    primaryLawOwnsStatutoryPropositionIsTrue :
      primaryLawOwnsStatutoryProposition ≡ true
    calibrationCaseOwnsQueenslandStatutoryText : Bool
    calibrationCaseOwnsQueenslandStatutoryTextIsFalse :
      calibrationCaseOwnsQueenslandStatutoryText ≡ false
    dashiOwnsCompilerAbstraction : Bool
    dashiOwnsCompilerAbstractionIsTrue : dashiOwnsCompilerAbstraction ≡ true
    parserOwnsLegalAuthority : Bool
    parserOwnsLegalAuthorityIsFalse : parserOwnsLegalAuthority ≡ false

canonicalAttributionBoundary : AttributionBoundary
canonicalAttributionBoundary =
  attributionBoundary true refl false refl true refl false refl
