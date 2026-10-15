module DASHI.Cognition.PalantirMissionExpansionContestability20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PalantirInstalledBaseProcurementPersistence20261015Exact as Persistence
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Capability

------------------------------------------------------------------------
-- PALANTIR MISSION EXPANSION / SUBJECT CONTESTABILITY — 2026-10-15
--
-- Two distinct live objects are preserved:
--   A. FOIA-released ICE/HSI emails concerning possible voter-roll processing
--      and potential entry into ELITE, a Palantir-supported enforcement tool;
--   B. Hilton v. Noem/Mullin litigation alleging observer information was
--      entered into Palantir-built ICE ICM and propagated into enforcement/
--      border-screening consequences.
--
-- Planning != deployment.  Plaintiff pleading != adjudicated fact.  Palantir
-- platform hosting/software != Palantir control of customer data or agency
-- decision authority.  These objects nevertheless directly test mission
-- expansion, data repurposing and subject remedy on concrete deployments.
------------------------------------------------------------------------

data MissionSurface : Set where
  originalImmigrationEnforcementUse : MissionSurface
  proposedElectionFraudUse : MissionSurface
  voterDataProcessing : MissionSurface
  pendingSystemEntry : MissionSurface
  actualSystemIngestion : MissionSurface
  observerDataCollection : MissionSurface
  observerICMRecord : MissionSurface
  crossSystemPropagation : MissionSurface
  subjectChallengeAndRemedy : MissionSurface

record MissionReceipt : Set where
  constructor mission-receipt
  field
    label : String
    date : String
    source : String
    sourceClass : String
    surface : MissionSurface
    boundedFinding : String
    paid : Bool
    actualDeploymentPaid : Bool
    adjudicatedPaid : Bool
open MissionReceipt public

eliteOriginalUse : MissionReceipt
eliteOriginalUse = mission-receipt
  "ELITE immigration-enforcement targeting use"
  "2026"
  "ICE/Palantir procurement and contemporary reporting on Enhanced Leads Identification & Targeting for Enforcement"
  "official procurement plus reporting"
  originalImmigrationEnforcementUse
  "ELITE is used as an immigration-enforcement lead/targeting environment, including target prioritisation/location and investigative workflow. This pays the baseline mission against which later proposed voter-fraud use is compared."
  true true false

voterFraudEmailMay2026 : MissionReceipt
voterFraudEmailMay2026 = mission-receipt
  "HSI voter-fraud processing / ELITE ingestion discussion"
  "2026-05-26"
  "ICE/HSI emails released to Democracy Forward by FOIA; reported verbatim by WIRED 8 Oct 2026"
  "government record released through FOIA"
  proposedElectionFraudUse
  "An HSI email with voter-fraud subject matter says iLab processing focused on DOJ voting rolls and USCIS data and describes coordination on ingesting processed voter-roll data into ELITE for lead management, analytical review and investigative tracking. This pays internal planning/processing and an intended ingestion path, not completed ingestion."
  true false false

voterDataScaleReceipt : MissionReceipt
voterDataScaleReceipt = mission-receipt
  "HSI voter-data acquisition scale"
  "2026"
  "Democracy Forward summary of ICE FOIA production, 7 Oct 2026"
  "advocacy organisation summarising government records"
  voterDataProcessing
  "Democracy Forward reports the produced HSI records as showing approximately 50.6 million DOJ voter-roll records, 26,235 USCIS-derived records and 48.4 million records from independent sources in the voter-fraud work. These figures are attributed to its review of the FOIA production and are not silently upgraded to an ICE-authored aggregate table here."
  true false false

elitePendingEntryJuly2026 : MissionReceipt
elitePendingEntryJuly2026 = mission-receipt
  "State data enriched and pending Palantir entry into ELITE"
  "2026-07-07"
  "ICE/HSI Fraud WAR email released by FOIA; WIRED/Democracy Forward reporting"
  "government record released through FOIA"
  pendingSystemEntry
  "A July update says six states had been enriched by iLab and were pending Palantir entry into ELITE. The carrier does not make clear exactly which enriched data fields were pending entry. This pays a near-deployment state, not completed voter-roll ingestion."
  true false false

palantirDenial : MissionReceipt
palantirDenial = mission-receipt
  "Palantir denies voter-roll integration into ELITE"
  "2026-10-08"
  "Palantir spokesperson statement to WIRED"
  "company statement"
  actualSystemIngestion
  "Palantir told WIRED that voter-roll data had never been integrated into ELITE. This is a first-party denial of completed voter-roll integration; it does not erase the separately paid ICE internal planning/enrichment/pending-entry records, nor does a company statement alone exhaustively establish all government-side data processing outside ELITE."
  true false false

hiltonCaseIdentity : MissionReceipt
hiltonCaseIdentity = mission-receipt
  "Hilton et al. v. Noem/Mullin civil-rights litigation"
  "2026-02-23 onward"
  "D. Me. case 2:26-cv-00092; docket and court orders"
  "federal court docket"
  subjectChallengeAndRemedy
  "Four Maine observers brought a federal civil-rights action challenging alleged surveillance/intimidation connected to observing immigration enforcement. The case and discovery/remedy process are paid procedural facts; disputed allegations are not adjudicated by case existence."
  true true false

observerICMAllegation : MissionReceipt
observerICMAllegation = mission-receipt
  "Observer information entered into ICE ICM"
  "2026"
  "partly unsealed filing in Hilton litigation; WIRED 2 Oct 2026 reporting from the filing"
  "plaintiff court filing / litigation allegation"
  observerICMRecord
  "A partly unsealed plaintiff filing alleges that federal agents created ICM records about people observing ICE activity, including photographs, licence-plate and related identifying information, in ICE's Palantir-built Investigative Case Management system. This pays the existence/content of the allegation, not final adjudication."
  true false false

observerPropagationAllegation : MissionReceipt
observerPropagationAllegation = mission-receipt
  "Observer-data propagation / border consequence allegation"
  "2026"
  "Hilton litigation filing as reported by WIRED; court docket discovery record"
  "plaintiff court filing / litigation allegation"
  crossSystemPropagation
  "The filing alleges observer information was used in facial-recognition and investigative workflows and that at least one observer faced continuing secondary-inspection consequences at the border. This is directly relevant to cross-system propagation and subject remedy, while remaining disputed/alleged absent adjudication or neutral operational logs."
  true false false

------------------------------------------------------------------------
-- Mission-expansion and contestability boundaries.
------------------------------------------------------------------------

record MissionBoundary : Set where
  constructor mission-boundary
  field
    baselineImmigrationMissionPaid : Bool
    voterFraudPlanningPaid : Bool
    voterDataProcessingPaid : Bool
    pendingELITEEntryPaid : Bool
    completedVoterRollIntegrationPaid : Bool
    palantirDenialPaid : Bool
    observerICMLitigationAllegationPaid : Bool
    observerCrossSystemConsequenceAllegationPaid : Bool
    finalMeritsAdjudicationPaid : Bool
    planningImpliesDeployment : Bool
    enrichedDataImpliesELITEIngestion : Bool
    litigationAllegationImpliesFact : Bool
    palantirSoftwareImpliesPalantirDecisionAuthority : Bool
    missionExpansionImpliesIllegality : Bool
open MissionBoundary public

canonicalMissionBoundary : MissionBoundary
canonicalMissionBoundary = mission-boundary
  true true true true false true true true false
  false false false false false

data PlanningImpliesDeployment : Set where
data PendingEntryImpliesCompletedIngestion : Set where
data PleadingImpliesAdjudicatedFact : Set where
data SoftwareImpliesAgencyDecisionAuthority : Set where
data MissionExpansionImpliesIllegality : Set where

planningDoesNotCreateDeployment : PlanningImpliesDeployment → ⊥
planningDoesNotCreateDeployment ()

pendingEntryDoesNotCreateIngestion : PendingEntryImpliesCompletedIngestion → ⊥
pendingEntryDoesNotCreateIngestion ()

pleadingDoesNotCreateAdjudicatedFact : PleadingImpliesAdjudicatedFact → ⊥
pleadingDoesNotCreateAdjudicatedFact ()

softwareDoesNotCreateDecisionAuthority : SoftwareImpliesAgencyDecisionAuthority → ⊥
softwareDoesNotCreateDecisionAuthority ()

missionExpansionDoesNotCreateIllegality : MissionExpansionImpliesIllegality → ⊥
missionExpansionDoesNotCreateIllegality ()

------------------------------------------------------------------------
-- The third-order hypothesis now has concrete same-system test objects.
------------------------------------------------------------------------

data MissionDebt : Set where
  fullFOIAEmailProduction : MissionDebt
  eliteActualDataTablesAndLogs : MissionDebt
  palantirEntryAttemptOutcome : MissionDebt
  voterFraudDecisionAndLeadOutputs : MissionDebt
  hiltonUnsealedOperationalExhibits : MissionDebt
  icmTecsPropagationLogs : MissionDebt
  subjectNoticeCorrectionDeletion : MissionDebt
  courtMeritsAndRemedy : MissionDebt

record MissionAcquisition : Set where
  constructor mission-acquisition
  field
    debt : MissionDebt
    priority : Nat
    instruction : String
open MissionAcquisition public

canonicalMissionAcquisition : List MissionAcquisition
canonicalMissionAcquisition =
  mission-acquisition fullFOIAEmailProduction 100
    "Acquire/index the complete ICE/HSI FOIA production and bind each voter-data/ELITE proposition to exact government-record page IDs rather than media excerpts or advocacy summaries." ∷
  mission-acquisition eliteActualDataTablesAndLogs 100
    "Acquire ELITE data-source/configuration tables and ingestion/audit logs sufficient to determine whether voter-roll-derived records ever entered ELITE and, if so, which fields, dates and users." ∷
  mission-acquisition palantirEntryAttemptOutcome 100
    "Resolve the July 'pending Palantir entry' state to completed entry, rejection, cancellation or technical deferral; Palantir's public denial and ICE internal planning must remain simultaneously represented until same-object records resolve the endpoint." ∷
  mission-acquisition hiltonUnsealedOperationalExhibits 100
    "Acquire the newly unsealed Hilton filing and underlying government discovery exhibits showing the exact ICM records, labels, photos, plate queries, facial-recognition requests and agency actors rather than relying on reporting summaries." ∷
  mission-acquisition icmTecsPropagationLogs 99
    "Resolve whether/how the alleged ICM observer records propagated to TECS or secondary-inspection systems using same-person audit/event records; platform interoperability alone is insufficient." ∷
  mission-acquisition subjectNoticeCorrectionDeletion 99
    "Determine what notice, inspection, correction, deletion, appeal and audit avenues the named observers actually had for the ICM/related records; user audit tooling is not subject contestability." ∷
  mission-acquisition voterFraudDecisionAndLeadOutputs 99
    "Acquire investigative lead/output and case-disposition records to distinguish bulk data processing from actual individual classification, referral, enforcement or prosecution outcomes." ∷
  mission-acquisition courtMeritsAndRemedy 98
    "Track Hilton merits findings and any injunction/expungement/correction orders; filing allegations and preliminary procedural orders do not settle factual or legal merits."
  ∷ []
