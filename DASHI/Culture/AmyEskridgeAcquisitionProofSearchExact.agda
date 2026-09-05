module DASHI.Culture.AmyEskridgeAcquisitionProofSearchExact where

------------------------------------------------------------------------
-- AMY ESKRIDGE PROOF-DIRECTED EVIDENCE ACQUISITION
--
-- Turns the current evidence ledger into targeted acquisition obligations.
-- Every target below is generated because the relevant record is currently
-- `notLocated` in AmyEskridgeEvidenceHyperfabricExact.  The module does not
-- assert that the record exists.  A later `knownAbsent` receipt closes only the
-- exact acquisition branch; a `present` receipt supplies new evidence that may
-- selectively reopen dependent interpretations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.EvidenceHyperfabricExact as Evidence
import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Culture.AmyEskridgeEvidenceHyperfabricExact as Eskridge

------------------------------------------------------------------------
-- Concrete acquisition targets.
------------------------------------------------------------------------

policeReportTarget : Acquisition.AcquisitionTarget
policeReportTarget =
  Acquisition.acquisition-target
    "police incident / calls-for-service records"
    "Any contemporaneous law-enforcement report, call-for-service entry, case number, narrative, or supplement concerning alleged residential intrusions or the death investigation."
    "identify jurisdiction, date/location, case number, then use the responsible agency's records process"
    "lawful archival / court / counsel-assisted request if ordinary public access is unavailable"
    "agency records law, privacy restrictions, victim/family standing, subpoena or court process where applicable"

apartmentManagementTarget : Acquisition.AcquisitionTarget
apartmentManagementTarget =
  Acquisition.acquisition-target
    "apartment-management records"
    "Contemporaneous complaint, maintenance, key/access, security, CCTV, email, or incident records concerning the reported intrusions."
    "identify apartment complex and occupancy dates; request retained management/security records from the lawful custodian"
    "recover copies from former resident, ex-partner, insurer, counsel, email/cloud archive, or other lawful source"
    "property-management privacy, retention, and access rules"

exPartnerTarget : Acquisition.AcquisitionTarget
exPartnerTarget =
  Acquisition.acquisition-target
    "ex-partner witness account"
    "Independent first-person account of the charger, window, headphones/intimate-property scenes and any vehicle/surveillance observations personally witnessed."
    "identify and seek a voluntary interview or already-public recorded statement"
    "locate contemporaneous messages or declarations authored by the witness"
    "voluntary participation; no harassment, impersonation, coercion, or private-data intrusion"

originalMediaMetadataTarget : Acquisition.AcquisitionTarget
originalMediaMetadataTarget =
  Acquisition.acquisition-target
    "original media and metadata"
    "Original photographs, videos, audio, messages and native metadata rather than transformed screenshots/transcripts alone."
    "obtain original files from lawful custodian/source and preserve hashes/metadata"
    "authenticated export from device/cloud/account custodian"
    "consent, platform/account authority, chain-of-custody and privacy constraints"

autopsyTarget : Acquisition.AcquisitionTarget
autopsyTarget =
  Acquisition.acquisition-target
    "autopsy / postmortem examination record"
    "Autopsy or postmortem report, including wound description, trajectory, pathology findings and examiner conclusions if such a record exists."
    "identify medical examiner/coroner custodian and use lawful record-access process"
    "court/counsel/family-authorised access where public release is restricted"
    "medical-record, coroner, privacy and public-record restrictions"

toxicologyTarget : Acquisition.AcquisitionTarget
toxicologyTarget =
  Acquisition.acquisition-target
    "toxicology record"
    "Toxicology testing and results associated with the death investigation, if performed."
    "request through the medical-examiner/coroner record custodian"
    "court/counsel/family-authorised access where public release is restricted"
    "medical-record, coroner and privacy restrictions"

ballisticsTarget : Acquisition.AcquisitionTarget
ballisticsTarget =
  Acquisition.acquisition-target
    "firearm / ballistics / GSR evidence"
    "Firearm identification, ownership/custody, latent/DNA testing, cartridge/casing evidence, gunshot-residue testing and related forensic reports if generated."
    "identify investigating law-enforcement agency and case number; request releasable forensic reports"
    "court/counsel process for nonpublic records"
    "criminal-investigation record restrictions and lawful access requirements"

------------------------------------------------------------------------
-- Current ledger mechanically generates obligations.
------------------------------------------------------------------------

policeReportObligation : Acquisition.AcquisitionObligation policeReportTarget
policeReportObligation = Acquisition.obligationFromNotLocated policeReportTarget

apartmentManagementObligation :
  Acquisition.AcquisitionObligation apartmentManagementTarget
apartmentManagementObligation =
  Acquisition.obligationFromNotLocated apartmentManagementTarget

exPartnerObligation : Acquisition.AcquisitionObligation exPartnerTarget
exPartnerObligation = Acquisition.obligationFromNotLocated exPartnerTarget

originalMediaMetadataObligation :
  Acquisition.AcquisitionObligation originalMediaMetadataTarget
originalMediaMetadataObligation =
  Acquisition.obligationFromNotLocated originalMediaMetadataTarget

autopsyObligation : Acquisition.AcquisitionObligation autopsyTarget
autopsyObligation = Acquisition.obligationFromNotLocated autopsyTarget

toxicologyObligation : Acquisition.AcquisitionObligation toxicologyTarget
toxicologyObligation = Acquisition.obligationFromNotLocated toxicologyTarget

ballisticsObligation : Acquisition.AcquisitionObligation ballisticsTarget
ballisticsObligation = Acquisition.obligationFromNotLocated ballisticsTarget

------------------------------------------------------------------------
-- Ledger receipts: current public-record state really is notLocated on the
-- institutional/forensic targets already represented in the case fixture.
------------------------------------------------------------------------

policeLedgerSeedsSearch :
  Eskridge.publicPoliceReport Eskridge.currentPublicRecordLedger ≡ Evidence.notLocated
policeLedgerSeedsSearch = refl

apartmentLedgerSeedsSearch :
  Eskridge.publicApartmentManagementComplaint Eskridge.currentPublicRecordLedger
  ≡ Evidence.notLocated
apartmentLedgerSeedsSearch = refl

autopsyLedgerSeedsSearch :
  Eskridge.publicAutopsy Eskridge.currentPublicRecordLedger ≡ Evidence.notLocated
autopsyLedgerSeedsSearch = refl

toxicologyLedgerSeedsSearch :
  Eskridge.publicToxicology Eskridge.currentPublicRecordLedger ≡ Evidence.notLocated
toxicologyLedgerSeedsSearch = refl

ballisticsLedgerSeedsSearch :
  Eskridge.publicBallisticsOrGSR Eskridge.currentPublicRecordLedger ≡ Evidence.notLocated
ballisticsLedgerSeedsSearch = refl

------------------------------------------------------------------------
-- Dependency graph: acquired records affect only declared downstream consumers.
------------------------------------------------------------------------

data InvestigationArtifact : Set where
  policeRecordArtifact
  apartmentRecordArtifact
  exPartnerWitnessArtifact
  originalMediaArtifact
  autopsyArtifact
  toxicologyArtifact
  ballisticsArtifact
  intrusionPatternAssessment
  threatChronologyAssessment
  deathMechanismAssessment
  deathMannerAssessment
  caseHyperfabricAssessment
  : InvestigationArtifact

data EskridgeDepends : InvestigationArtifact → InvestigationArtifact → Set where
  policeToIntrusion : EskridgeDepends policeRecordArtifact intrusionPatternAssessment
  apartmentToIntrusion : EskridgeDepends apartmentRecordArtifact intrusionPatternAssessment
  exPartnerToIntrusion : EskridgeDepends exPartnerWitnessArtifact intrusionPatternAssessment
  mediaToIntrusion : EskridgeDepends originalMediaArtifact intrusionPatternAssessment
  mediaToThreatChronology : EskridgeDepends originalMediaArtifact threatChronologyAssessment
  autopsyToMechanism : EskridgeDepends autopsyArtifact deathMechanismAssessment
  toxicologyToMechanism : EskridgeDepends toxicologyArtifact deathMechanismAssessment
  ballisticsToMechanism : EskridgeDepends ballisticsArtifact deathMechanismAssessment
  mechanismToManner : EskridgeDepends deathMechanismAssessment deathMannerAssessment
  intrusionToCase : EskridgeDepends intrusionPatternAssessment caseHyperfabricAssessment
  threatToCase : EskridgeDepends threatChronologyAssessment caseHyperfabricAssessment
  mannerToCase : EskridgeDepends deathMannerAssessment caseHyperfabricAssessment

eskridgeAcquisitionGraph :
  Acquisition.AcquisitionDependencyGraph InvestigationArtifact
eskridgeAcquisitionGraph =
  Acquisition.acquisition-dependency-graph
    EskridgeDepends
    "Amy Eskridge evidence acquisition reverse-dependency graph"

policeRecordReopensIntrusionAssessment :
  Acquisition.SelectiveAcquisitionReopening
    eskridgeAcquisitionGraph policeRecordArtifact intrusionPatternAssessment
policeRecordReopensIntrusionAssessment =
  Acquisition.oneEdgeAcquisitionReopening policeToIntrusion

autopsyReopensDeathMechanism :
  Acquisition.SelectiveAcquisitionReopening
    eskridgeAcquisitionGraph autopsyArtifact deathMechanismAssessment
autopsyReopensDeathMechanism =
  Acquisition.oneEdgeAcquisitionReopening autopsyToMechanism

autopsyReopensCaseTransitively :
  Dependency.ReopeningObligation
    EskridgeDepends autopsyArtifact caseHyperfabricAssessment
autopsyReopensCaseTransitively =
  Dependency.obligationsCompose
    (Dependency.oneEdgeCreatesReopeningObligation autopsyToMechanism)
    (Dependency.obligationsCompose
      (Dependency.oneEdgeCreatesReopeningObligation mechanismToManner)
      (Dependency.oneEdgeCreatesReopeningObligation mannerToCase))

------------------------------------------------------------------------
-- Acquisition-state firewall.
------------------------------------------------------------------------

record EskridgeAcquisitionBoundary : Set where
  constructor eskridge-acquisition-boundary
  field
    notLocatedPoliceRecordCreatesAcquisitionObligation : Bool
    notLocatedPoliceRecordCreatesAcquisitionObligationIsTrue :
      notLocatedPoliceRecordCreatesAcquisitionObligation ≡ true
    notLocatedAutopsyCreatesAcquisitionObligation : Bool
    notLocatedAutopsyCreatesAcquisitionObligationIsTrue :
      notLocatedAutopsyCreatesAcquisitionObligation ≡ true
    knownAbsentWouldCloseOnlyExactAcquisitionBranch : Bool
    knownAbsentWouldCloseOnlyExactAcquisitionBranchIsTrue :
      knownAbsentWouldCloseOnlyExactAcquisitionBranch ≡ true
    knownAbsentWouldAutomaticallyProveOfficialNarrative : Bool
    knownAbsentWouldAutomaticallyProveOfficialNarrativeIsFalse :
      knownAbsentWouldAutomaticallyProveOfficialNarrative ≡ false
    acquiredRecordReopensOnlyDependencyReachableConsumers : Bool
    acquiredRecordReopensOnlyDependencyReachableConsumersIsTrue :
      acquiredRecordReopensOnlyDependencyReachableConsumers ≡ true
    lawfulAccessConstraintsRemainPartOfSearchRoute : Bool
    lawfulAccessConstraintsRemainPartOfSearchRouteIsTrue :
      lawfulAccessConstraintsRemainPartOfSearchRoute ≡ true

canonicalEskridgeAcquisitionBoundary : EskridgeAcquisitionBoundary
canonicalEskridgeAcquisitionBoundary =
  eskridge-acquisition-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
