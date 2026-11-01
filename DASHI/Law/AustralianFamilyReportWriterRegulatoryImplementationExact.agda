module DASHI.Law.AustralianFamilyReportWriterRegulatoryImplementationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- AUSTRALIAN FAMILY-REPORT-WRITER REGULATORY IMPLEMENTATION STATUS
--
-- This owner records the difference between:
--   enacted primary legislation,
--   a regulation-making power,
--   a regulations instrument,
--   an implementing provision actually located in that instrument,
--   designation of a regulator,
--   operation of recognition/monitoring/complaints/consequence machinery.
--
-- It is deliberately fail-closed.  A bounded search that does not locate an
-- implementing provision is not a theorem that no such provision/instrument
-- exists anywhere or will never exist.
------------------------------------------------------------------------

data RegulatoryLayer : Set where
  primaryActLayer : RegulatoryLayer
  enablingPowerLayer : RegulatoryLayer
  regulationsInstrumentLayer : RegulatoryLayer
  implementingProvisionLayer : RegulatoryLayer
  regulatorDesignationLayer : RegulatoryLayer
  recognitionSchemeLayer : RegulatoryLayer
  complaintSchemeLayer : RegulatoryLayer
  compliancePublicationLayer : RegulatoryLayer
  courtConsequenceLayer : RegulatoryLayer

------------------------------------------------------------------------
-- Primary-source attribution.
------------------------------------------------------------------------

familyLawActPartIIIAASource : Attribution.AttributedSource
familyLawActPartIIIAASource = Attribution.mkNoDOISource
  "Commonwealth of Australia"
  "Family Law Act 1975, Part IIIAA—Family report writers, including section 11K"
  "Federal Register of Legislation"
  "current compilation surface searched 2026-09-14"
  "https://www.legislation.gov.au/C2004A00275/latest/text"
  Attribution.governmentSource
  "primary legislation paying the existence and scope of the Part IIIAA / section 11K regulation-making power only; does not instantiate subordinate regulations or prove compliance by any writer"
  Attribution.publicAttribution

familyLawRegulations2024Source : Attribution.AttributedSource
familyLawRegulations2024Source = Attribution.mkNoDOISource
  "Commonwealth of Australia"
  "Family Law Regulations 2024"
  "Federal Register of Legislation, title F2024L01638"
  "latest Register details surface searched 2026-09-14; page identifies compilation F2025C00562 C01"
  "https://www.legislation.gov.au/F2024L01638/latest/text"
  Attribution.governmentSource
  "current regulations surface searched for family-report-writer / section-11K implementation terms; non-location is bounded search evidence, not proof of absence"
  Attribution.publicAttribution

familyLawAmendmentAct2023Schedule7Source : Attribution.AttributedSource
familyLawAmendmentAct2023Schedule7Source = Attribution.mkNoDOISource
  "Commonwealth of Australia"
  "Family Law Amendment Act 2023, Schedule 7—Family report writers"
  "Federal Register of Legislation, Act No. 87 of 2023"
  "2023"
  "https://www.legislation.gov.au/C2023A00087/latest/text"
  Attribution.governmentSource
  "historical amending Act paying the enactment genealogy of Part IIIAA and section 11K; it does not pay a later implementing regulation"
  Attribution.publicAttribution

attorneyGeneralFamilyReportWriterConsultationSource : Attribution.AttributedSource
attorneyGeneralFamilyReportWriterConsultationSource = Attribution.mkNoDOISource
  "Australian Government Attorney-General's Department"
  "Family report writers—consultation on proposed standards and requirements"
  "Attorney-General's Department consultation material"
  "2023"
  "https://consultations.ag.gov.au/families-and-marriage/family-report-writers/"
  Attribution.governmentSource
  "historical implementation-context source describing the legislative amendment as a first step and detailed standards/requirements as a regulations-stage task; does not establish current 2026 implementation status by itself"
  Attribution.publicAttribution

regulatoryImplementationSourceAtlas : Attribution.AttributedSourceAtlas
regulatoryImplementationSourceAtlas = Attribution.mkSourceAtlas
  "Australian family-report-writer regulatory implementation atlas"
  "DASHI.Law.AustralianFamilyReportWriterRegulatoryImplementationExact"
  (familyLawActPartIIIAASource
    ∷ familyLawRegulations2024Source
    ∷ familyLawAmendmentAct2023Schedule7Source
    ∷ attorneyGeneralFamilyReportWriterConsultationSource
    ∷ [])
  "primary Act + current Federal Register regulations surface + amending-Act genealogy + historical implementation context; no citation creates implementation, compliance, breach or legal authority beyond its source role"

------------------------------------------------------------------------
-- Current principal-instrument search receipt.
------------------------------------------------------------------------

record RegulatoryImplementationSearchReceipt : Set where
  constructor regulatoryImplementationSearchReceipt
  field
    searchDate : String
    actPartIIIAALocated : Bool
    actSection11KLocated : Bool
    regulationsTitleId : String
    regulationsLatestVersionLabelLocated : String
    regulationsMarkedInForce : Bool
    exactFamilyReportWriterTextLocatedInCurrentRegulations : Bool
    exactSection11KTextLocatedInCurrentRegulations : Bool
    implementingProvisionLocatedByThisSearch : Bool
    regulatorDesignationLocatedByThisSearch : Bool
    recognitionSchemeLocatedByThisSearch : Bool
    complaintSchemeLocatedByThisSearch : Bool
    courtDisregardRuleLocatedByThisSearch : Bool
    negativeSearchScope : String
    searchProvesAbsence : Bool

open RegulatoryImplementationSearchReceipt public

currentRegulatoryImplementationSearchReceipt : RegulatoryImplementationSearchReceipt
currentRegulatoryImplementationSearchReceipt =
  regulatoryImplementationSearchReceipt
    "2026-09-14"
    true
    true
    "F2024L01638"
    "F2025C00562 C01"
    true
    false
    false
    false
    false
    false
    false
    false
    "Federal Register latest Family Law Regulations 2024 text/details surface; exact searches for 'family report writer' and '11K' returned no match. This receipt is search-bounded and does not exclude another instrument, amendment, future instrument, indexing gap or later source."
    false

------------------------------------------------------------------------
-- Widened search receipt.
--
-- A separate public-web search was run across legislation.gov.au / AGD for
-- family-report-writer regulations and section-11K implementation.  It located
-- the Act, Schedule-7 amending genealogy and historical consultation context,
-- but no separate implementing instrument in the returned result set.  Search
-- engine coverage is not the Federal Register itself and cannot prove absence.
------------------------------------------------------------------------

record BroaderRegulatorySearchReceipt : Set where
  constructor broaderRegulatorySearchReceipt
  field
    broaderSearchDate : String
    federalRegisterDomainSearchPerformed : Bool
    attorneyGeneralDomainSearchPerformed : Bool
    enablingActResultsLocated : Bool
    schedule7AmendingActLocated : Bool
    historicalConsultationLocated : Bool
    separateImplementingInstrumentLocated : Bool
    searchResultSetExhaustive : Bool
    broaderSearchAbsenceClaim : Bool
    broaderSearchScope : String

open BroaderRegulatorySearchReceipt public

currentBroaderRegulatorySearchReceipt : BroaderRegulatorySearchReceipt
currentBroaderRegulatorySearchReceipt =
  broaderRegulatorySearchReceipt
    "2026-09-14"
    true
    true
    true
    true
    true
    false
    false
    false
    "Public domain-restricted search across legislation.gov.au and ag.gov.au for family-report-writer / section-11K regulations. Returned sources included the Family Law Act 1975, Family Law Amendment Act 2023 Schedule 7 and AGD consultation material; no separate implementing instrument appeared in the returned result set. This is acquisition metadata only and is not exhaustive Federal Register proof."

------------------------------------------------------------------------
-- Canonical paid/unpaid coordinates.
------------------------------------------------------------------------

partIIIAAEnacted : Bool
partIIIAAEnacted = true

section11KEnablingPowerPaid : Bool
section11KEnablingPowerPaid = true

currentRegulationsSurfaceChecked : Bool
currentRegulationsSurfaceChecked = true

broaderImplementationSearchPerformed : Bool
broaderImplementationSearchPerformed = true

implementingProvisionLocated : Bool
implementingProvisionLocated =
  implementingProvisionLocatedByThisSearch currentRegulatoryImplementationSearchReceipt

broaderSearchLocatedImplementingInstrument : Bool
broaderSearchLocatedImplementingInstrument =
  separateImplementingInstrumentLocated currentBroaderRegulatorySearchReceipt

broaderSearchProvesAbsence : Bool
broaderSearchProvesAbsence =
  broaderSearchAbsenceClaim currentBroaderRegulatorySearchReceipt

regulatorDesignationPaid : Bool
regulatorDesignationPaid =
  regulatorDesignationLocatedByThisSearch currentRegulatoryImplementationSearchReceipt

recognitionSchemePaid : Bool
recognitionSchemePaid =
  recognitionSchemeLocatedByThisSearch currentRegulatoryImplementationSearchReceipt

complaintSchemePaid : Bool
complaintSchemePaid =
  complaintSchemeLocatedByThisSearch currentRegulatoryImplementationSearchReceipt

courtDisregardRulePaid : Bool
courtDisregardRulePaid =
  courtDisregardRuleLocatedByThisSearch currentRegulatoryImplementationSearchReceipt

absenceOfImplementingProvisionProved : Bool
absenceOfImplementingProvisionProved =
  searchProvesAbsence currentRegulatoryImplementationSearchReceipt

------------------------------------------------------------------------
-- WrongType / promotion boundaries.
------------------------------------------------------------------------

data EnablingPowerAutomaticallyOperativeRegime : Set where
data NegativeSearchAutomaticallyProvesAbsence : Set where
data RegulatorConceptAutomaticallyDesignatesRegulator : Set where
data RecognitionPowerAutomaticallyCreatesRecognitionScheme : Set where
data PossibleCourtConsequenceAutomaticallyOperativeRule : Set where
data ProfessionalRegistrationAutomaticallyFamilyReportRecognition : Set where
data RegulationsInstrumentAutomaticallyImplementsEveryActPower : Set where
data PublicSearchResultsAutomaticallyExhaustFederalRegister : Set where

enablingPowerDoesNotAutomaticallyCreateOperativeRegime :
  EnablingPowerAutomaticallyOperativeRegime → ⊥
enablingPowerDoesNotAutomaticallyCreateOperativeRegime ()

negativeSearchDoesNotProveAbsence :
  NegativeSearchAutomaticallyProvesAbsence → ⊥
negativeSearchDoesNotProveAbsence ()

regulatorConceptDoesNotAutomaticallyDesignateRegulator :
  RegulatorConceptAutomaticallyDesignatesRegulator → ⊥
regulatorConceptDoesNotAutomaticallyDesignateRegulator ()

recognitionPowerDoesNotAutomaticallyCreateRecognitionScheme :
  RecognitionPowerAutomaticallyCreatesRecognitionScheme → ⊥
recognitionPowerDoesNotAutomaticallyCreateRecognitionScheme ()

possibleCourtConsequenceDoesNotAutomaticallyBecomeOperativeRule :
  PossibleCourtConsequenceAutomaticallyOperativeRule → ⊥
possibleCourtConsequenceDoesNotAutomaticallyBecomeOperativeRule ()

professionalRegistrationDoesNotAutomaticallyCreateFamilyReportRecognition :
  ProfessionalRegistrationAutomaticallyFamilyReportRecognition → ⊥
professionalRegistrationDoesNotAutomaticallyCreateFamilyReportRecognition ()

regulationsInstrumentDoesNotAutomaticallyImplementEveryActPower :
  RegulationsInstrumentAutomaticallyImplementsEveryActPower → ⊥
regulationsInstrumentDoesNotAutomaticallyImplementEveryActPower ()

publicSearchResultsDoNotAutomaticallyExhaustFederalRegister :
  PublicSearchResultsAutomaticallyExhaustFederalRegister → ⊥
publicSearchResultsDoNotAutomaticallyExhaustFederalRegister ()

record RegulatoryImplementationBoundary : Set where
  constructor regulatoryImplementationBoundary
  field
    primaryActEnacted : Bool
    enablingPowerLocated : Bool
    regulationsInstrumentLocatedAndInForce : Bool
    principalRegulationsSearched : Bool
    broaderPublicSearchPerformed : Bool
    implementingProvisionLocatedFlag : Bool
    regulatorDesignationPaidFlag : Bool
    recognitionSchemePaidFlag : Bool
    complaintSchemePaidFlag : Bool
    courtDisregardRulePaidFlag : Bool
    negativeSearchProvesAbsenceFlag : Bool
    publicSearchExhaustsFederalRegister : Bool
    citationCreatesImplementation : Bool
    citationCreatesCompliance : Bool
    citationCreatesBreach : Bool

open RegulatoryImplementationBoundary public

canonicalRegulatoryImplementationBoundary : RegulatoryImplementationBoundary
canonicalRegulatoryImplementationBoundary =
  regulatoryImplementationBoundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
