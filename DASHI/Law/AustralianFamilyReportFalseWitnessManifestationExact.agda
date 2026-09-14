module DASHI.Law.AustralianFamilyReportFalseWitnessManifestationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Law.AustralianFamilyReportWriterIntegrityExact as AU

------------------------------------------------------------------------
-- FALSE WITNESS: SOURCE-BOUNDED MANIFESTATION FIXTURE
--
-- This file does not identify the pseudonymised practitioner and does not decide
-- misconduct, legal breach, admissibility, negligence, causation, or truth of a
-- whole report.  It binds reported manifestations to evidence classes and to
-- candidate integrity axes already owned by AustralianFamilyReportWriterIntegrity.
--
-- The publication title "False Witness" is retained as a title only; it is not
-- promoted into a factual/legal classification of the practitioner.
------------------------------------------------------------------------

parentAustralianIntegrityBoundary : AU.AustralianFamilyReportWriterBoundary
parentAustralianIntegrityBoundary = AU.canonicalAustralianFamilyReportWriterBoundary

------------------------------------------------------------------------
-- Source attribution.
------------------------------------------------------------------------

abcFalseWitnessSource : Attribution.AttributedSource
abcFalseWitnessSource = Attribution.mkNoDOISource
  "Heidi Davoren for Background Briefing"
  "Recordings expose family court expert witness under investigation by Australian Health Practitioner Regulation Agency"
  "ABC News / Background Briefing"
  "2023"
  "https://www.abc.net.au/news/2023-06-19/family-court-report-writer-recording-expert-witness-ahpra/102185414"
  Attribution.newsSource
  "investigative journalism reporting participant accounts and content described as captured in hours of recordings; article updated 5 October 2023; does not supply DASHI raw-recording custody, a judicial finding, or an adverse regulatory finding"
  Attribution.publicAttribution

fcfcoaFalseWitnessResponseSource : Attribution.AttributedSource
fcfcoaFalseWitnessResponseSource = Attribution.mkNoDOISource
  "Federal Circuit and Family Court of Australia (Division 1 and Division 2)"
  "Statement by The Federal Circuit and Family Court of Australia - Response to ABC Report - False Witness"
  "FCFCOA media release"
  "2023"
  "https://www.fcfcoa.gov.au/news-and-media-centre/media-releases/statement-190623"
  Attribution.institutionalSource
  "institutional response recording concern about the alleged conduct and clarifying that the psychologist operated privately and was not employed or engaged by the Courts; concern is not an adjudicated breach finding"
  Attribution.publicAttribution

falseWitnessSourceAtlas : Attribution.AttributedSourceAtlas
falseWitnessSourceAtlas = Attribution.mkSourceAtlas
  "False Witness manifestation source atlas"
  "DASHI.Law.AustralianFamilyReportFalseWitnessManifestationExact"
  (abcFalseWitnessSource ∷ fcfcoaFalseWitnessResponseSource ∷ [])
  "ABC investigative manifestation plus Court institutional response; raw recordings, court report, regulator primary file and later regulator outcome remain separate acquisition coordinates"

------------------------------------------------------------------------
-- Evidence classes.
------------------------------------------------------------------------

data ManifestationEvidenceClass : Set where
  recordingBackedReportedConduct : ManifestationEvidenceClass
  participantAccount : ManifestationEvidenceClass
  abcJournalisticSynthesis : ManifestationEvidenceClass
  courtInstitutionalResponse : ManifestationEvidenceClass
  regulatorStatusReportedByABC : ManifestationEvidenceClass

data ManifestationIncident : Set where
  reportedSolicitorContact : ManifestationIncident
  reportedPsychometricPressure : ManifestationIncident
  reportedDifferentialTestAdministration : ManifestationIncident
  reportedFamilyViolenceMaterialDismissal : ManifestationIncident
  reportedTherapeuticIntervention : ManifestationIncident
  reportedEarlyCourtOutcomeView : ManifestationIncident
  reportedPublicSessionContext : ManifestationIncident

manifestationPrimaryAxis :
  ManifestationIncident → AU.FamilyAssessmentIntegrityAxis
manifestationPrimaryAxis reportedSolicitorContact = AU.exParteIntegrity
manifestationPrimaryAxis reportedPsychometricPressure = AU.psychometricUseAdequacy
manifestationPrimaryAxis reportedDifferentialTestAdministration = AU.psychometricUseAdequacy
manifestationPrimaryAxis reportedFamilyViolenceMaterialDismissal = AU.riskInformationCoverage
manifestationPrimaryAxis reportedTherapeuticIntervention = AU.forensicTherapeuticRoleSeparation
manifestationPrimaryAxis reportedEarlyCourtOutcomeView = AU.recommendationTiming
manifestationPrimaryAxis reportedPublicSessionContext = AU.methodologicalAdequacy

record ManifestationEntry : Set where
  constructor manifestationEntry
  field
    incident : ManifestationIncident
    evidenceClass : ManifestationEvidenceClass
    sourceReference : String
    primaryAxis : AU.FamilyAssessmentIntegrityAxis
    caseApplicationPaid : Bool
    authoritativeBreachFindingPaid : Bool

solicitorContactEntry : ManifestationEntry
solicitorContactEntry = manifestationEntry
  reportedSolicitorContact
  recordingBackedReportedConduct
  "ABC 2023 False Witness reporting / recording-described source"
  AU.exParteIntegrity
  false
  false

psychometricPressureEntry : ManifestationEntry
psychometricPressureEntry = manifestationEntry
  reportedPsychometricPressure
  recordingBackedReportedConduct
  "ABC 2023 False Witness reporting / recording-described source"
  AU.psychometricUseAdequacy
  false
  false

differentialAdministrationEntry : ManifestationEntry
differentialAdministrationEntry = manifestationEntry
  reportedDifferentialTestAdministration
  participantAccount
  "ABC 2023 participant accounts"
  AU.psychometricUseAdequacy
  false
  false

familyViolenceMaterialEntry : ManifestationEntry
familyViolenceMaterialEntry = manifestationEntry
  reportedFamilyViolenceMaterialDismissal
  participantAccount
  "ABC 2023 participant account"
  AU.riskInformationCoverage
  false
  false

therapeuticInterventionEntry : ManifestationEntry
therapeuticInterventionEntry = manifestationEntry
  reportedTherapeuticIntervention
  recordingBackedReportedConduct
  "ABC 2023 recording-described conduct"
  AU.forensicTherapeuticRoleSeparation
  false
  false

earlyOutcomeViewEntry : ManifestationEntry
earlyOutcomeViewEntry = manifestationEntry
  reportedEarlyCourtOutcomeView
  recordingBackedReportedConduct
  "ABC 2023 recording-described conduct"
  AU.recommendationTiming
  false
  false

------------------------------------------------------------------------
-- Acquisition / institutional frontier.
------------------------------------------------------------------------

record FalseWitnessFrontier : Set where
  constructor falseWitnessFrontier
  field
    abcArticleAcquired : Bool
    fcfcoaResponseAcquired : Bool
    rawRecordingsAcquiredByDashi : Bool
    fullRecordingCoverageEstablished : Bool
    familyReportAcquired : Bool
    primaryAHPRAInvestigationRecordAcquired : Bool
    investigationReportedByABC : Bool
    laterRegulatoryOutcomeLocatedInCurrentSearch : Bool
    absenceOfLaterRegulatoryOutcomeProved : Bool
    protectedIdentityRetainedOpaque : Bool
    identityResolutionAttempted : Bool
    privatePsychologistNotCourtEmployedOrEngaged : Bool
    courtInstitutionalConcernRecorded : Bool
    courtResponseEstablishedBreach : Bool
    abcArticleIsJudicialFinding : Bool
    publicationTitleClassifiesWitnessFalse : Bool

open FalseWitnessFrontier public

currentFalseWitnessFrontier : FalseWitnessFrontier
currentFalseWitnessFrontier = falseWitnessFrontier
  true
  true
  false
  false
  false
  false
  true
  false
  false
  true
  false
  true
  true
  false
  false
  false

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data PublicationTitleAutomaticallyProvesFalseWitness : Set where
data InstitutionalConcernAutomaticallyEstablishesBreach : Set where
data ReportedInvestigationAutomaticallyAdverseFinding : Set where
data ABCReportAutomaticallyJudicialFinding : Set where
data RecordingBackedReportAutomaticallyRawRecordingCustody : Set where
data PrivateExpertAutomaticallyCourtEmployee : Set where

publicationTitleDoesNotProveFalseWitness :
  PublicationTitleAutomaticallyProvesFalseWitness → ⊥
publicationTitleDoesNotProveFalseWitness ()

institutionalConcernDoesNotEstablishBreach :
  InstitutionalConcernAutomaticallyEstablishesBreach → ⊥
institutionalConcernDoesNotEstablishBreach ()

reportedInvestigationDoesNotProveAdverseFinding :
  ReportedInvestigationAutomaticallyAdverseFinding → ⊥
reportedInvestigationDoesNotProveAdverseFinding ()

abcReportDoesNotBecomeJudicialFinding :
  ABCReportAutomaticallyJudicialFinding → ⊥
abcReportDoesNotBecomeJudicialFinding ()

recordingBackedReportingDoesNotCreateRawCustody :
  RecordingBackedReportAutomaticallyRawRecordingCustody → ⊥
recordingBackedReportingDoesNotCreateRawCustody ()

privateExpertDoesNotAutomaticallyBecomeCourtEmployee :
  PrivateExpertAutomaticallyCourtEmployee → ⊥
privateExpertDoesNotAutomaticallyBecomeCourtEmployee ()
