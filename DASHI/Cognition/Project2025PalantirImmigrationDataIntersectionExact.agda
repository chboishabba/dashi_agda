module DASHI.Cognition.Project2025PalantirImmigrationDataIntersectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.Project2025ImplementationIncidenceAtlasExact as Project2025
import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Systemic

------------------------------------------------------------------------
-- PROJECT 2025 x PALANTIR x IMMIGRATION DATA/ENFORCEMENT INTERSECTION
--
-- Separates:
--   policy demand for integrated enforcement/data capacity
--   actual Palantir/ICE procurement and deployed capability
--   vendor-selection causation.
--
-- The first two are source-paid independently.  Their intersection is a valid
-- systemic-incidence object.  No receipt here establishes that Project 2025,
-- Heritage, or a named author selected Palantir or caused a particular award.
------------------------------------------------------------------------

data IntersectionSurface : Set where
  project2025ImmigrationAgencyIntegration : IntersectionSurface
  project2025LawEnforcementDatabaseAccess : IntersectionSurface
  palantirICEICM : IntersectionSurface
  palantirImmigrationOS : IntersectionSurface
  palantirEROTargetingOrder2026 : IntersectionSurface
  policyCapabilityIntersection : IntersectionSurface
  project2025VendorSelectionUnpaid : IntersectionSurface

record IntersectionReceipt : Set where
  constructor intersection-receipt
  field
    surface : IntersectionSurface
    sourceIdentity : String
    sourceClass : String
    boundedFinding : String
    relationPaid : Bool
    directVendorSelectionCausationPaid : Bool
    wrongdoingPaid : Bool
open IntersectionReceipt public

project2025IntegrationReceipt : IntersectionReceipt
project2025IntegrationReceipt = intersection-receipt
  project2025ImmigrationAgencyIntegration
  "Heritage Foundation, Mandate for Leadership, Department of Homeland Security chapter"
  "primary policy blueprint"
  "Project 2025 recommends remerging/core-integrating USCIS, ICE and CBP immigration functions and strengthening cooperation and information sharing."
  true false false

project2025DatabaseReceipt : IntersectionReceipt
project2025DatabaseReceipt = intersection-receipt
  project2025LawEnforcementDatabaseAccess
  "Heritage Foundation, Mandate for Leadership, Department of Homeland Security chapter"
  "primary policy blueprint"
  "Project 2025 recommends designating USCIS as Intelligence Community-adjacent with access to national-security and law-enforcement databases, alongside stronger fraud-detection/vetting functions."
  true false false

palantirICMReceipt : IntersectionReceipt
palantirICMReceipt = intersection-receipt
  palantirICEICM
  "ICE contract records / Palantir Investigative Case Management contract lineage"
  "official procurement record"
  "ICE has long used Palantir's Investigative Case Management system as a data/investigative platform. This pays vendor/capability deployment, not policy authorship."
  true false false

immigrationOSReceipt : IntersectionReceipt
immigrationOSReceipt = intersection-receipt
  palantirImmigrationOS
  "ICE limited-sources justification for ICM / ImmigrationOS continued support"
  "official procurement justification"
  "ICE procurement materials describe ImmigrationOS functions including identification/prioritisation of enforcement targets, field targeting data, apprehension support, custody information, deportation-status tracking and self-deportation visibility."
  true false false

palantirERO2026Receipt : IntersectionReceipt
palantirERO2026Receipt = intersection-receipt
  palantirEROTargetingOrder2026
  "USAspending award 70CTD026FC0000012"
  "official federal spending record"
  "ICE awarded Palantir Technologies an approximately USD 86.27m order on 2026-04-30 for Enforcement and Removal Operations-related information-technology work."
  true false false

policyCapabilityReceipt : IntersectionReceipt
policyCapabilityReceipt = intersection-receipt
  policyCapabilityIntersection
  "cross-source typed intersection"
  "DASHI reconstruction over separately paid Project 2025 policy and ICE/Palantir procurement receipts"
  "The policy blueprint demands greater enforcement/data integration while current procurement supplies integrated targeting/data capability. This is a same-domain policy-capability intersection worthy of incidence analysis, not proof that the blueprint caused the vendor award."
  true false false

vendorSelectionBoundaryReceipt : IntersectionReceipt
vendorSelectionBoundaryReceipt = intersection-receipt
  project2025VendorSelectionUnpaid
  "current acquisition boundary"
  "negative/non-promotion receipt"
  "No source in the current receipt set establishes that Heritage Foundation, Project 2025, or a Project 2025 author selected Palantir, required Palantir, or caused the ICE awards."
  false false false

------------------------------------------------------------------------
-- First / second / third-order incidence.
------------------------------------------------------------------------

palantirImmigrationFirstOrder : Systemic.SystemicLeverageCandidate
palantirImmigrationFirstOrder = Systemic.systemic-leverage-candidate
  "Project 2025 policy demand x Palantir/ICE immigration-data capability"
  Systemic.firstOrder
  Systemic.procurementContracting
  "Which policy requirements and executive priorities are implemented through specific data, targeting and case-management procurements?"
  "ICE/ERO gains integrated operational capability; the vendor receives contract revenue and embedded platform position."
  "People processed by the enforcement system may bear privacy, error, detention/removal or due-process burdens; each outcome requires person/process-specific evidence."
  "Who controls data sources, access permissions, target criteria, audit trails, human review and correction mechanisms?"
  "procurement statements of work, system documentation, privacy impact assessments, audit logs, contract modifications and enforcement outcome data"
  true false false

palantirImmigrationSecondOrder : Systemic.SystemicLeverageCandidate
palantirImmigrationSecondOrder = Systemic.systemic-leverage-candidate
  "Project 2025 policy demand x Palantir/ICE immigration-data capability"
  Systemic.secondOrder
  Systemic.exitConstraint
  "Does integration of previously separate data/enforcement functions increase switching costs, operational dependence or the ease of scaling enforcement?"
  "Agency operators and incumbent vendors may gain coordination and platform option value; magnitude and exclusivity remain acquisition questions."
  "Affected people, competing vendors, oversight bodies or future administrations may face reduced practical exit/reversibility if data/workflows become tightly integrated."
  "Who owns schemas/configuration, can export data, replace the vendor, change scoring rules, inspect provenance or unwind integrations?"
  "BPA/limited-source justifications, architecture diagrams, interoperability/export clauses, renewal history, migration costs and oversight reports"
  false false false

palantirImmigrationThirdOrder : Systemic.SystemicLeverageCandidate
palantirImmigrationThirdOrder = Systemic.systemic-leverage-candidate
  "Project 2025 policy demand x Palantir/ICE immigration-data capability"
  Systemic.thirdOrder
  Systemic.institutionalControl
  "Does the combined policy/data infrastructure change durable state capacity for population identification, eligibility classification, enforcement prioritisation or cross-agency information sharing?"
  "Future administrations or agencies may inherit expanded technical capacity independent of the original policy coalition."
  "Long-run burdens may include path dependence, mission expansion, false-positive propagation or weakened practical contestability; none is inferred without receipts."
  "Which capabilities persist after policy leadership changes, and what statutory, technical or contractual checks constrain repurposing?"
  "longitudinal contract/system use, successor-policy records, privacy/civil-liberties audits, litigation, error studies and decommissioning/migration evidence"
  false false false

record Project2025PalantirBoundary : Set where
  constructor project2025-palantir-boundary
  field
    project2025DataIntegrationDemandPaid : Bool
    palantirICECapabilityPaid : Bool
    palantir2026EROAwardPaid : Bool
    policyCapabilityIntersectionPaid : Bool
    project2025SelectedPalantir : Bool
    sharedTrumpAdministrationContextEqualsCoordination : Bool
    procurementEqualsPolicyAuthorship : Bool
    capabilityEqualsAbuse : Bool
open Project2025PalantirBoundary public

canonicalProject2025PalantirBoundary : Project2025PalantirBoundary
canonicalProject2025PalantirBoundary = project2025-palantir-boundary
  true true true true false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PolicyDemandImpliesVendorSelection : Set where
data CapabilityImpliesAbuse : Set where
data ProcurementImpliesPolicyAuthorship : Set where
data IntegratedDataImpliesCorrectClassification : Set where
data SameAdministrationImpliesCoordination : Set where

policyDemandDoesNotCreateVendorSelection : PolicyDemandImpliesVendorSelection → ⊥
policyDemandDoesNotCreateVendorSelection ()

capabilityDoesNotCreateAbuse : CapabilityImpliesAbuse → ⊥
capabilityDoesNotCreateAbuse ()

procurementDoesNotCreatePolicyAuthorship : ProcurementImpliesPolicyAuthorship → ⊥
procurementDoesNotCreatePolicyAuthorship ()

integrationDoesNotCreateCorrectClassification : IntegratedDataImpliesCorrectClassification → ⊥
integrationDoesNotCreateCorrectClassification ()

sameAdministrationDoesNotCreateCoordination : SameAdministrationImpliesCoordination → ⊥
sameAdministrationDoesNotCreateCoordination ()
