module DASHI.Law.QueenslandButForSourceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- QUEENSLAND FACTUAL CAUSATION SOURCE / ATTRIBUTION BOUNDARY
--
-- Attribution policy:
--   * Current Queensland legislation owns Queensland statutory propositions.
--   * High Court cases below are calibrations concerning NSW Civil Liability
--     Act 2002 s 5D; they are not represented as the textual source of
--     Queensland Civil Liability Act 2003 s 11.
--   * DASHI owns the typed records, counterfactual fibres, compilers and
--     non-promotion firewalls built around those source propositions.
--   * Statutory authority is not statutory applicability: ss 4, 5 and 7 remain
--     external prerequisites/boundaries for a concrete matter.
------------------------------------------------------------------------

data SourceRole : Set where
  primaryQueenslandLegislation : SourceRole
  highCourtCalibration : SourceRole
  dashiOriginalAbstraction : SourceRole


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
  "Civil Liability Act 2003 (Qld), current text"
  "Civil Liability Act 2003 (Qld) ss 4, 5, 7, 10, 11, 12"
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-2003-016"
  "Primary Queensland source. Section 11 owns the necessary-condition factual-causation and separate scope-of-liability propositions, exceptional route and subjective harmed-person counterfactual rule; s 12 owns the causation onus/balance-of-probabilities proposition; s 10 owns the avoidability-alone boundary; ss 4, 5 and 7 bound application, cause-of-action and non-codification claims."

strongCalibration : LegalSourceAttribution
strongCalibration = legalSourceAttribution
  highCourtCalibration
  "Strong v Woolworths Limited"
  "[2012] HCA 5"
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/strong-v-woolworths-limited"
  "High Court calibration concerning factual causation, necessary condition and evidentiary inference under Civil Liability Act 2002 (NSW) s 5D; not the textual source of Queensland s 11 and not a substitute for a Queensland applicability receipt."

wallaceCalibration : LegalSourceAttribution
wallaceCalibration = legalSourceAttribution
  highCourtCalibration
  "Wallace v Kam"
  "[2013] HCA 19"
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/wallace-v-kam"
  "High Court calibration separating factual causation from scope of liability under Civil Liability Act 2002 (NSW) s 5D; not the textual source of Queensland s 11 and not a substitute for a Queensland applicability receipt."

dashiButForArchitecture : LegalSourceAttribution
dashiButForArchitecture = legalSourceAttribution
  dashiOriginalAbstraction
  "DASHI legal but-for causation architecture"
  "DASHI-original"
  "DASHI/Law/LegalFactualCausationButForExact.agda"
  "Typed breach-correction intervention, counterfactual fibre, robust/selected/underidentified distinctions, WrongType element compiler, parser bridge and non-promotion firewalls are DASHI abstractions, not language attributed to the legislature or High Court."

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

    actCreatesIndependentCauseOfAction : Bool
    actCreatesIndependentCauseOfActionIsFalse :
      actCreatesIndependentCauseOfAction ≡ false

    actIsCompleteCodification : Bool
    actIsCompleteCodificationIsFalse : actIsCompleteCodification ≡ false

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
    false refl
    false refl
    queenslandCivilLiabilityAct

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data HighCourtNSWCaseIsTextualSourceOfQueenslandSection11 : Set where
data DASHICompilerIsLegislativeText : Set where
data ParserOutputIsLegalSourceAuthority : Set where
data SourceBackedPropositionTransfersAllDASHIAbstractionsToSource : Set where
data SourceAuthorityAutomaticallyEstablishesApplicability : Set where

data Section11CreatesCauseOfAction : Set where

data Section11IsCompleteCodification : Set where

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

sourceAuthorityDoesNotAutoEstablishApplicability :
  SourceAuthorityAutomaticallyEstablishesApplicability → ⊥
sourceAuthorityDoesNotAutoEstablishApplicability ()

section11DoesNotCreateCauseOfAction : Section11CreatesCauseOfAction → ⊥
section11DoesNotCreateCauseOfAction ()

section11DoesNotClaimCompleteCodification : Section11IsCompleteCodification → ⊥
section11DoesNotClaimCompleteCodification ()

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
    sourceAuthorityEqualsApplicability : Bool
    sourceAuthorityEqualsApplicabilityIsFalse : sourceAuthorityEqualsApplicability ≡ false

canonicalAttributionBoundary : AttributionBoundary
canonicalAttributionBoundary =
  attributionBoundary true refl false refl true refl false refl false refl
