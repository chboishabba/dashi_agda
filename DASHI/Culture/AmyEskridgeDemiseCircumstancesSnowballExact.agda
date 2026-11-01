module DASHI.Culture.AmyEskridgeDemiseCircumstancesSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: CIRCUMSTANCES-OF-DEMISE SNOWBALL
--
-- Public/lawful evidence only.  This owner keeps source role, proposition role,
-- and evidentiary strength distinct.  It is deliberately parallel to the
-- scientific memorial snowball but no scientific result can pay a forensic
-- proposition and no forensic allegation can pay a scientific mechanism leaf.
------------------------------------------------------------------------

data DemiseSourceRole : Set where
  familyMemorialSource : DemiseSourceRole
  amyFirstPersonSource : DemiseSourceRole
  secondaryNewsReport : DemiseSourceRole
  institutionalOversightSource : DemiseSourceRole
  primaryForensicRecord : DemiseSourceRole

data DemiseProposition : Set where
  dateOfDeath : DemiseProposition
  reportedOfficialManner : DemiseProposition
  reportedMechanismOfDeath : DemiseProposition
  preDeathIntrusionReport : DemiseProposition
  federalReviewContext : DemiseProposition
  researchLinkedDeath : DemiseProposition
  actorIdentity : DemiseProposition

data InspectionStatus : Set where
  locatedAndInspected : InspectionStatus
  reportedBySecondarySource : InspectionStatus
  notPubliclyLocated : InspectionStatus
  knownAbsent : InspectionStatus

data EvidentiaryEffect : Set where
  establishesNarrowProposition : EvidentiaryEffect
  recordsSpeakerStatementOnly : EvidentiaryEffect
  recordsReportedOfficialCharacterizationOnly : EvidentiaryEffect
  recordsOversightContextOnly : EvidentiaryEffect
  opensAcquisitionObligation : EvidentiaryEffect

record DemiseSnowballAtom : Set where
  constructor demise-snowball-atom
  field
    sourceRole : DemiseSourceRole
    proposition : DemiseProposition
    locator : String
    sourceSummary : String
    inspectionStatus : InspectionStatus
    evidentiaryEffect : EvidentiaryEffect
    sourceMayBeRetainedOutOfOrder : Bool
    createsCulpritInference : Bool
    createsResearchLinkInference : Bool

open DemiseSnowballAtom public

familyObituaryDateAtom : DemiseSnowballAtom
familyObituaryDateAtom =
  demise-snowball-atom
    familyMemorialSource
    dateOfDeath
    "AL.com / Legacy family obituary, published June 2022"
    "Family obituary states Amy Catherine Eskridge died Saturday, 11 June 2022, aged 34; it supplies no cause or manner of death."
    locatedAndInspected
    establishesNarrowProposition
    true false false

amyIntrusionStatementAtom : DemiseSnowballAtom
amyIntrusionStatementAtom =
  demise-snowball-atom
    amyFirstPersonSource
    preDeathIntrusionReport
    "archived Amy Eskridge Zoom/interview, approximately 38:07 onward"
    "Amy states that people repeatedly entered the apartment she shared with her then-partner while both were away and describes a cut micro-USB charger and later disturbances."
    locatedAndInspected
    recordsSpeakerStatementOnly
    true false false

reportedMannerAtom : DemiseSnowballAtom
reportedMannerAtom =
  demise-snowball-atom
    secondaryNewsReport
    reportedOfficialManner
    "Fox News / Fox Nation reporting, April-May 2026"
    "Secondary reporting characterizes the 2022 death as a self-inflicted gunshot wound / suicide while also noting that limited official detail has been publicly released."
    reportedBySecondarySource
    recordsReportedOfficialCharacterizationOnly
    true false false

houseOversightContextAtom : DemiseSnowballAtom
houseOversightContextAtom =
  demise-snowball-atom
    institutionalOversightSource
    federalReviewContext
    "U.S. House Committee on Oversight and Government Reform letters dated 20 April 2026"
    "Official committee correspondence investigates unconfirmed public reporting about deaths/disappearances of people with access to sensitive scientific information and requests agency briefings; the letter is context, not an Amy-specific forensic finding."
    locatedAndInspected
    recordsOversightContextOnly
    true false false

autopsyAcquisitionAtom : DemiseSnowballAtom
autopsyAcquisitionAtom =
  demise-snowball-atom
    primaryForensicRecord
    reportedMechanismOfDeath
    "autopsy / postmortem examination record"
    "No authenticated public autopsy/postmortem carrier has been located in the current public-source review; lawful primary-record acquisition remains open."
    notPubliclyLocated
    opensAcquisitionObligation
    true false false

toxicologyAcquisitionAtom : DemiseSnowballAtom
toxicologyAcquisitionAtom =
  demise-snowball-atom
    primaryForensicRecord
    reportedMechanismOfDeath
    "toxicology record"
    "No authenticated public toxicology carrier has been located in the current public-source review; lawful primary-record acquisition remains open."
    notPubliclyLocated
    opensAcquisitionObligation
    true false false

policeAcquisitionAtom : DemiseSnowballAtom
policeAcquisitionAtom =
  demise-snowball-atom
    primaryForensicRecord
    reportedOfficialManner
    "police incident / death-investigation file"
    "No authenticated public police investigative file has been located in the current public-source review; lawful primary-record acquisition remains open."
    notPubliclyLocated
    opensAcquisitionObligation
    true false false

record DemiseSnowballBoundary : Set where
  constructor demise-snowball-boundary
  field
    obituaryDateEqualsForensicCause : Bool
    firstPersonIntrusionStatementEqualsIndependentIntrusionProof : Bool
    secondaryReportedSuicideEqualsInspectedPrimaryForensicRecord : Bool
    federalReviewContextEqualsCaseConnection : Bool
    federalReviewContextEqualsResearchLinkedDeath : Bool
    scientificNoveltyEqualsDeathCausation : Bool
    notPubliclyLocatedEqualsKnownAbsent : Bool
    laterPrimaryRecordMayReopenDependentAssessment : Bool
    atomsMayAccumulateOutOfDependencyOrder : Bool

canonicalDemiseSnowballBoundary : DemiseSnowballBoundary
canonicalDemiseSnowballBoundary =
  demise-snowball-boundary false false false false false false false true true
