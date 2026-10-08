module DASHI.Governance.AnarchyRulesSupplementalResearchArtifactsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- SUPPLEMENTAL RESEARCH ARTIFACTS FROM THE USER-SUPPLIED RESHARE PACKAGE.
--
-- These files are not OWS General Assembly minutes. They are research
-- administration / instrument artifacts associated with the broader project.
-- Their existence and wording may document research design, but a blank
-- questionnaire is not participant response data and a consent/information
-- sheet is not an empirical result.
------------------------------------------------------------------------

record SupplementalPackage : Set where
  constructor supplementalPackage
  field
    suppliedOrigin : String
    localFilename : String
    packageBytes : Nat
    packageSha256 : String
    nonDirectoryMemberCount : Nat

open SupplementalPackage public

visitDatesParticipationPackage : SupplementalPackage
visitDatesParticipationPackage =
  supplementalPackage
    "https://reshare.ukdataservice.ac.uk/853247/"
    "VisitDates_ParticipationSheets.zip"
    102012
    "3a5ae76be371ddf6ee44ec6ae08c6a9a74e0cb478c99cefcae7052acbb989b31"
    3

record SupplementalArtifact : Set where
  constructor supplementalArtifact
  field
    artifactLabel : String
    artifactRole : String
    artifactBytes : Nat
    artifactSha256 : String
    sourceQualifiedDescription : String

open SupplementalArtifact public

branchVisitDates : SupplementalArtifact
branchVisitDates =
  supplementalArtifact
    "Copy of Branch visit dates.txt"
    "fieldwork scheduling artifact"
    776
    "37b12462ff0dd93eddfa75ee8807f72a1ca609d0ec36ba0ef42b25a0903f110f"
    "lists possible/preferred branch visit dates; this is scheduling metadata rather than governance-outcome evidence"

informationSheetIWW : SupplementalArtifact
informationSheetIWW =
  supplementalArtifact
    "Information Sheet IWW.rtf"
    "participant information / ethics artifact"
    24054
    "47d4b85355aa38250404b815aafcd52070d45979a4f1fe92703c04f72ecd62d2"
    "describes the Anarchy as Constitutional Principle project, ESRC code ES/N006860/1, researchers and informed-consent / archiving conditions"

informedConsentForm : SupplementalArtifact
informedConsentForm =
  supplementalArtifact
    "Informed Consent Form.rtf"
    "participant consent artifact"
    1007183
    "33b90ec39b023948a676ad16cbc19b0b2a6daa1b15e4689874e5e08167e18b39"
    "records the consent form template for observation/recording under anonymisation conditions; template content is not evidence that any named person consented"

membershipSurveyQuestionnaire : SupplementalArtifact
membershipSurveyQuestionnaire =
  supplementalArtifact
    "Membership_SurveyQuestionnaire.pdf"
    "IWW membership survey questionnaire"
    223551
    "09bb4c4be0cc7a68218a3d99a95546dfc24b0360bb9c33e1747f810f8bd8c1b6"
    "questionnaire states that the research concerns participatory budgeting and decision making in the IWW and asks respondents about when decision making works well or is difficult; the blank questionnaire is an instrument, not response data"

record SupplementalResearchBoundary : Set where
  constructor supplementalResearchBoundary
  field
    supplementalArtifactsAreOWSGAMinutes : Bool
    questionnaireContainsParticipantResponses : Bool
    consentTemplateProvesSpecificParticipantConsent : Bool
    schedulingFileIsGovernanceOutcomeEvidence : Bool
    supplementalArtifactsValidateOccupyScaling : Bool
    researchInstrumentQuestionsCountAsEmpiricalAnswers : Bool

    supplementalArtifactProvenancePinned : Bool

open SupplementalResearchBoundary public

canonicalSupplementalBoundary : SupplementalResearchBoundary
canonicalSupplementalBoundary =
  supplementalResearchBoundary
    false false false false false false true

canonicalSupplementalResearchReceipt : GenericReceipt.GenericReceipt
canonicalSupplementalResearchReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Anarchy Rules supplemental research-artifact provenance"
    "DASHI.Governance.AnarchyRulesSupplementalResearchArtifactsExact"
    "canonicalSupplementalBoundary"
    "pins the uploaded fieldwork scheduling, participant-information, consent-template and IWW questionnaire artifacts by byte count/SHA-256 and records their bounded research-design roles"
    "research instruments and administration artifacts are not OWS minutes, not participant response data, not proof of specific consent, and not empirical validation of Occupy governance scaling"
    "agda -i . DASHI/Governance/AnarchyRulesSupplementalResearchArtifactsRegression.agda"
