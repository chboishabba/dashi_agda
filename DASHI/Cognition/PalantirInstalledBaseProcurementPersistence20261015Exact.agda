module DASHI.Cognition.PalantirInstalledBaseProcurementPersistence20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PalantirTIAFinanceStateCapacityCrossPollination20261015Exact as Cross
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Capability
import DASHI.Governance.PalantirProcurementLegibilityAdapterExact as Legibility

------------------------------------------------------------------------
-- PALANTIR INSTALLED-BASE / PROCUREMENT PERSISTENCE — 2026-10-15
--
-- This owner pays a bounded persistence mechanism:
--   early intelligence-user feedback -> product adaptation -> repeated agency
--   adoption -> later migration/exit difficulty evidence -> large umbrella BPA
--   with concrete component calls.
--
-- It also retains counterevidence: interoperability initiatives and examples of
-- contested/blocked procurement. Persistence therefore remains an empirical,
-- deployment-specific question rather than a universal lock-in theorem.
------------------------------------------------------------------------

data PersistenceSurface : Set where
  userFeedbackDevelopment : PersistenceSurface
  earlyAgencyAdoption : PersistenceSurface
  migrationExitDifficulty : PersistenceSurface
  umbrellaProcurementVehicle : PersistenceSurface
  componentTaskOrder : PersistenceSurface
  limitedSourceCall : PersistenceSurface
  userAuditControlDevelopment : PersistenceSurface
  interoperabilityInitiative : PersistenceSurface
  contestedProcurement : PersistenceSurface

record PersistenceReceipt : Set where
  constructor persistence-receipt
  field
    label : String
    date : String
    source : String
    surface : PersistenceSurface
    boundedFinding : String
    paid : Bool
    lockInProved : Bool
open PersistenceReceipt public

earlyCIAFeedback : PersistenceReceipt
earlyCIAFeedback = persistence-receipt
  "Early intelligence-user feedback loop"
  "2000s"
  "Wired, 'Palantir Technologies spots patterns to solve crimes and track terrorists' (2012)"
  userFeedbackDevelopment
  "Wired reports In-Q-Tel investment gave Palantir access to frontline intelligence analysts; Karp estimated more than 300 meetings with likely users, with repeated product changes based on feedback before and during early government adoption. This pays iterative customer-product adaptation, not TIA succession or government ownership of the product."
  true false

earlyAgencyPropagation : PersistenceReceipt
earlyAgencyPropagation = persistence-receipt
  "Early government propagation"
  "2008-2012"
  "Wired 2012 Palantir history"
  earlyAgencyAdoption
  "Wired reports an initial government contract followed by additional contracts and adoption across CIA/intelligence, military and law-enforcement customers, with word-of-mouth among users described as a growth mechanism. This pays repeated institutional adoption at a historical level."
  true false

policingMigrationDifficulty : PersistenceReceipt
policingMigrationDifficulty = persistence-receipt
  "Documented policing migration/exit difficulty"
  "2009-2017 record reviewed in 2017 Wired investigation"
  "Wired, 'How Peter Thiel's Secretive Data Company Pushed Into Policing'"
  migrationExitDifficulty
  "Public-record reporting documented agencies becoming operationally dependent on Palantir-linked regional data systems and described migration away from the system as difficult without loss of critical data, alongside opaque/expanding costs. This pays a historical exit-cost mechanism, not a universal finding for every Palantir deployment."
  true false

dhsBPA2026 : PersistenceReceipt
dhsBPA2026 = persistence-receipt
  "DHS-wide Palantir BPA"
  "2026-02"
  "USAspending parent PIID 70RTAC26A00000001; SAM limited-sources justification FY25-00257"
  umbrellaProcurementVehicle
  "DHS established a single-award Palantir BPA for commercial software licences, maintenance and implementation services department-wide with a potential ceiling of USD1 billion and a five-year ordering horizon. The umbrella vehicle lowers transaction friction for component purchases; it does not itself require every DHS component to buy Palantir or prove unlawful vendor lock-in."
  true false

iceEROModernization2026 : PersistenceReceipt
iceEROModernization2026 = persistence-receipt
  "ICE ERO modernisation call"
  "2026-05-05"
  "USAspending PIID 70CTD026FC0000012 under parent 70RTAC26A00000001"
  componentTaskOrder
  "ICE obligated USD86,271,599.30 for Enforcement Removal Operations modernisation and operational capability for its enforcement case-management system on the case-management and analytics platform. This is a concrete component call under the DHS-wide Palantir vehicle."
  true false

cisaSaaSCall2026 : PersistenceReceipt
cisaSaaSCall2026 = persistence-receipt
  "CISA Palantir SaaS call"
  "2026-09-29"
  "USAspending PIID 70RCSJ26FC0000028 under parent 70RTAC26A00000001"
  limitedSourceCall
  "CISA obligated USD32,106,349.78 for Palantir software-as-a-service under the same DHS parent BPA. USAspending marks the call as subject to fair-opportunity procedures while recording a limited-sources field of 'only one source - other'. This pays another component-level use of the common vehicle; legal sufficiency or competitive harm is not inferred."
  true false

iceAuditControls2026 : PersistenceReceipt
iceAuditControls2026 = persistence-receipt
  "ICE-oriented user-auditing controls"
  "2026-05"
  "Wired reporting on Palantir ICE hack week"
  userAuditControlDevelopment
  "Reporting describes Palantir building customer-facing user auditing/session-log controls for ICE/DHS-related deployments amid internal concern. This pays a capability/oversight response surface; it does not prove that affected subjects receive notice, access, correction or appeal rights."
  true false

armyRightToIntegrate2026 : PersistenceReceipt
armyRightToIntegrate2026 = persistence-receipt
  "Army Right to Integrate interoperability sprint"
  "2026-05-06"
  "Palantir first-party press release: Palantir Joins U.S. Army and Industry Partners for 'Right to Integrate' Hackathon Sprint"
  interoperabilityInitiative
  "Palantir publicly describes participation with the U.S. Army and industry partners in a Right to Integrate effort aimed at defense-wide interoperability. This is counterevidence against assuming the vendor's objective or every deployment is closed-system dependence. It does not independently prove practical data/configuration portability, low switching cost or compliance with specific exit clauses."
  true false

londonPoliceBlockedContract2026 : PersistenceReceipt
londonPoliceBlockedContract2026 = persistence-receipt
  "London police Palantir procurement blocked/challenged"
  "2026-10-14"
  "Reuters reporting on Palantir/MOPAC settlement over proposed Metropolitan Police contract"
  contestedProcurement
  "Reuters reports that a proposed roughly GBP50m Metropolitan Police Palantir contract was blocked by London's mayoral policing office, litigated and later settled with both sides withdrawing allegations. This pays a concrete example that procurement can be contested/blocked; it neither proves the procurement process was substantively optimal nor negates switching costs in already-installed systems."
  true false

record PersistenceBoundary : Set where
  constructor persistence-boundary
  field
    iterativeGovernmentFeedbackPaid : Bool
    repeatedAgencyAdoptionPaid : Bool
    historicalMigrationDifficultyPaid : Bool
    dhsUmbrellaVehiclePaid : Bool
    multipleComponentCallsPaid : Bool
    interoperabilityCounterevidencePaid : Bool
    contestedProcurementCounterexamplePaid : Bool
    allDeploymentsLockedIn : Bool
    lockInUnlawful : Bool
    procurementVehicleEqualsPolicyAuthorship : Bool
    userAuditLogsEqualSubjectContestability : Bool
    commonBPAEqualsCommonOperationalPurpose : Bool
    interoperabilityClaimImpliesEasyMigration : Bool
open PersistenceBoundary public

canonicalPersistenceBoundary : PersistenceBoundary
canonicalPersistenceBoundary = persistence-boundary
  true true true true true true true false false false false false false

data RepeatedAdoptionImpliesUniversalLockIn : Set where
data UmbrellaVehicleImpliesPolicyAuthorship : Set where
data AuditLogsImpliesSubjectRemedy : Set where
data SameBPAImpliesSameOperationalPurpose : Set where
data InteroperabilityInitiativeImpliesEasyExit : Set where

repeatedAdoptionDoesNotCreateUniversalLockIn : RepeatedAdoptionImpliesUniversalLockIn → ⊥
repeatedAdoptionDoesNotCreateUniversalLockIn ()

umbrellaVehicleDoesNotCreatePolicyAuthorship : UmbrellaVehicleImpliesPolicyAuthorship → ⊥
umbrellaVehicleDoesNotCreatePolicyAuthorship ()

auditLogsDoNotCreateSubjectRemedy : AuditLogsImpliesSubjectRemedy → ⊥
auditLogsDoNotCreateSubjectRemedy ()

sameBPADoesNotCreateOperationalPurpose : SameBPAImpliesSameOperationalPurpose → ⊥
sameBPADoesNotCreateOperationalPurpose ()

interoperabilityInitiativeDoesNotCreateEasyExit : InteroperabilityInitiativeImpliesEasyExit → ⊥
interoperabilityInitiativeDoesNotCreateEasyExit ()

------------------------------------------------------------------------
-- Persistence/lock-in is now quantifiable rather than purely conceptual.
------------------------------------------------------------------------

data PersistenceDebt : Set where
  parentBPAFullTerms : PersistenceDebt
  renewalAndPriorVehicleHistory : PersistenceDebt
  schemaConfigurationOwnership : PersistenceDebt
  exportMigrationRights : PersistenceDebt
  actualMigrationAttempts : PersistenceDebt
  limitedSourceJustificationReasoning : PersistenceDebt
  componentRevenueAndBacklog : PersistenceDebt
  subjectRemedySameDeployment : PersistenceDebt

record PersistenceAcquisition : Set where
  constructor persistence-acquisition
  field
    debt : PersistenceDebt
    priority : Nat
    instruction : String
open PersistenceAcquisition public

canonicalPersistenceAcquisition : List PersistenceAcquisition
canonicalPersistenceAcquisition =
  persistence-acquisition parentBPAFullTerms 100
    "Acquire the complete DHS BPA and redacted limited-sources justification: scope, pricing, ordering, data/configuration rights, transition assistance, termination, interoperability and portability clauses." ∷
  persistence-acquisition renewalAndPriorVehicleHistory 100
    "Trace predecessor ICE/CBP/DHS Palantir awards into the 2026 BPA to measure incumbent continuity and renewal rather than treating the BPA as a fresh isolated award." ∷
  persistence-acquisition schemaConfigurationOwnership 100
    "Resolve who owns deployment ontologies, schemas, configurations, derived models and integration code on concrete ICE/CISA/Maven systems." ∷
  persistence-acquisition exportMigrationRights 100
    "Acquire export formats, migration/transition services and contractual data/configuration portability rights; legal portability and practical migration cost are distinct, and Right-to-Integrate participation does not settle either." ∷
  persistence-acquisition actualMigrationAttempts 99
    "Find attempted replacements, terminated deployments or migration projects and measure time, cost, data loss and operational disruption as direct exit-cost evidence; include successful migration counterexamples rather than sampling only failures." ∷
  persistence-acquisition limitedSourceJustificationReasoning 99
    "Read the full DHS limited-sources justification and component-call competition records to identify the stated technical/continuity reasons for Palantir specificity rather than inferring motive from the procurement code." ∷
  persistence-acquisition componentRevenueAndBacklog 98
    "Aggregate exact obligations, options and task-order backlog under the parent BPA by component/date while avoiding double counting ceiling value as revenue." ∷
  persistence-acquisition subjectRemedySameDeployment 98
    "On one ICE or other enforcement deployment, join user audit controls to subject notice, access, correction, appeal, deletion and judicial/administrative remedy records."
  ∷ []
