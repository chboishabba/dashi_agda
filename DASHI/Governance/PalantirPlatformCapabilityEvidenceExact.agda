module DASHI.Governance.PalantirPlatformCapabilityEvidenceExact where

------------------------------------------------------------------------
-- PALANTIR PLATFORM CAPABILITY EVIDENCE
--
-- This module strengthens the existing procurement-only adapter without
-- fabricating a deployment-specific subject/asymmetry theorem.  Official
-- Palantir documentation is sufficient to establish certain generic technical
-- capabilities: integrated datasets mapped into objects/properties/links,
-- Object Views, action/function layers for operational decision workflows,
-- granular object/property permissions, and comprehensive audit logs.
--
-- SOURCES / BOUNDED ROLES
--
-- Palantir Technologies Inc., "Ontology building - Overview", Foundry
-- documentation, accessed 2026; no DOI asserted.
-- Bounded role: Ontology maps integrated datasets/virtual tables/models to
-- objects, properties and links representing real-world counterparts and
-- supports action/function-driven operational workflows.
--
-- Palantir Technologies Inc., "Object permissioning - Overview" and
-- "Managing object security", Foundry documentation, accessed 2026;
-- no DOI asserted.
-- Bounded role: granular permissions can apply to ontology resources, objects,
-- links and properties, including row/cell-level visibility constraints.
--
-- Palantir Technologies Inc., "Core concepts - Object Views", Foundry
-- documentation, accessed 2026; no DOI asserted.
-- Bounded role: Object Views combine key object information, linked objects,
-- metrics, analyses, dashboards and applications around a particular object.
--
-- Palantir Technologies Inc., "Security auditing - Audit logs", Foundry
-- documentation, accessed 2026; no DOI asserted.
-- Bounded role: audit logs record user/action/time/resource context and may
-- include PII/search-query details; customers can export them for monitoring.
--
-- These documents describe platform capability. They do NOT establish what a
-- named government deployment ingests about a particular person, what decision
-- is taken about that person, or whether that person can inspect/correct/appeal
-- the representation. Those remain deployment-specific receipts.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record CapabilitySource : Set where
  constructor capabilitySource
  field
    institution : String
    title : String
    year : Nat
    doi : String
    boundedRole : String

open CapabilitySource public

data PlatformCapability : Set where
  integratedDataLayer : PlatformCapability
  objectPropertyLinkGraph : PlatformCapability
  objectCentricView : PlatformCapability
  operationalActionLayer : PlatformCapability
  granularObjectPropertyPermissioning : PlatformCapability
  auditLogging : PlatformCapability

data DeploymentReceiptKind : Set where
  subjectDataCategoryReceipt : DeploymentReceiptKind
  entityResolutionReceipt : DeploymentReceiptKind
  operationalDecisionUseReceipt : DeploymentReceiptKind
  subjectNoticeReceipt : DeploymentReceiptKind
  subjectInspectionReceipt : DeploymentReceiptKind
  subjectCorrectionReceipt : DeploymentReceiptKind
  subjectAppealReceipt : DeploymentReceiptKind

record CapabilityEvidence : Set where
  constructor capabilityEvidence
  field
    capability : PlatformCapability
    source : CapabilitySource
    genericPlatformCapabilityEstablished : Bool

open CapabilityEvidence public

ontologySource : CapabilitySource
ontologySource = capabilitySource
  "Palantir Technologies Inc."
  "Ontology building - Overview"
  2026
  "no DOI asserted"
  "generic Foundry Ontology object/property/link/action architecture; not deployment-specific data use"

permissionSource : CapabilitySource
permissionSource = capabilitySource
  "Palantir Technologies Inc."
  "Object permissioning - Overview / Managing object security"
  2026
  "no DOI asserted"
  "generic granular resource/object/property security controls; not evidence of subject contestability"

objectViewSource : CapabilitySource
objectViewSource = capabilitySource
  "Palantir Technologies Inc."
  "Core concepts - Object Views"
  2026
  "no DOI asserted"
  "generic object-centric information/workflow interface"

auditSource : CapabilitySource
auditSource = capabilitySource
  "Palantir Technologies Inc."
  "Security auditing - Audit logs"
  2026
  "no DOI asserted"
  "generic audit-log capability and customer monitoring/export architecture"

ontologyGraphCapability : CapabilityEvidence
ontologyGraphCapability = capabilityEvidence objectPropertyLinkGraph ontologySource true

operationalActionCapability : CapabilityEvidence
operationalActionCapability = capabilityEvidence operationalActionLayer ontologySource true

objectViewCapability : CapabilityEvidence
objectViewCapability = capabilityEvidence objectCentricView objectViewSource true

granularPermissionCapability : CapabilityEvidence
granularPermissionCapability = capabilityEvidence granularObjectPropertyPermissioning permissionSource true

auditCapability : CapabilityEvidence
auditCapability = capabilityEvidence auditLogging auditSource true

------------------------------------------------------------------------
-- Deployment-specific evidence remains unconstructed here.
------------------------------------------------------------------------

record DeploymentReceiptStatus : Set where
  constructor deploymentReceiptStatus
  field
    receiptKind : DeploymentReceiptKind
    installed : Bool

subjectDataCategoryStatus : DeploymentReceiptStatus
subjectDataCategoryStatus = deploymentReceiptStatus subjectDataCategoryReceipt false

operationalDecisionStatus : DeploymentReceiptStatus
operationalDecisionStatus = deploymentReceiptStatus operationalDecisionUseReceipt false

subjectInspectionStatus : DeploymentReceiptStatus
subjectInspectionStatus = deploymentReceiptStatus subjectInspectionReceipt false

subjectCorrectionStatus : DeploymentReceiptStatus
subjectCorrectionStatus = deploymentReceiptStatus subjectCorrectionReceipt false

subjectAppealStatus : DeploymentReceiptStatus
subjectAppealStatus = deploymentReceiptStatus subjectAppealReceipt false

data PlatformCapabilityPromotesDeploymentAsymmetry : Set where

data GranularPermissioningPromotesSubjectCorrection : Set where

data AuditLoggingPromotesPublicContestability : Set where

data ObjectGraphPromotesAbuse : Set where

capabilityDoesNotPromoteDeploymentAsymmetry :
  PlatformCapabilityPromotesDeploymentAsymmetry → ⊥
capabilityDoesNotPromoteDeploymentAsymmetry ()

permissioningDoesNotPromoteSubjectCorrection :
  GranularPermissioningPromotesSubjectCorrection → ⊥
permissioningDoesNotPromoteSubjectCorrection ()

auditLoggingDoesNotPromotePublicContestability :
  AuditLoggingPromotesPublicContestability → ⊥
auditLoggingDoesNotPromotePublicContestability ()

objectGraphDoesNotPromoteAbuse : ObjectGraphPromotesAbuse → ⊥
objectGraphDoesNotPromoteAbuse ()

record PalantirCapabilityBoundary : Set where
  constructor palantirCapabilityBoundary
  field
    objectLinkGraphCapabilityInstalled : Bool
    operationalWorkflowCapabilityInstalled : Bool
    granularPermissionCapabilityInstalled : Bool
    auditCapabilityInstalled : Bool
    deploymentSubjectDataReceiptInstalled : Bool
    deploymentDecisionUseReceiptInstalled : Bool
    subjectInspectionCorrectionAppealInstalled : Bool
    genericCapabilityEqualsObservedDeploymentAsymmetry : Bool
    genericCapabilityEqualsAbuse : Bool

canonicalPalantirCapabilityBoundary : PalantirCapabilityBoundary
canonicalPalantirCapabilityBoundary =
  palantirCapabilityBoundary true true true true false false false false false
