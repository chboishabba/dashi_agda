module DASHI.Education.DigitalESDSourceAuditAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale
import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards
import DASHI.Education.DigitalESDAuditDomainBoundaryReceiptExact as DomainBoundary
import DASHI.Education.DigitalESDSourceAuditHyperfabricExact as Hyperfabric

------------------------------------------------------------------------
-- COMPLETE CORE-AXIS COVERAGE
------------------------------------------------------------------------

record CompleteCoreAxisCoverage (source : Attr.AttributedSource) : Set where
  constructor complete-core-axis-coverage
  field
    educationalOutcomeReceipt : Scale.AxisVisibilityReceipt source
    educationalOutcomeAxisIsCorrect :
      Scale.axis educationalOutcomeReceipt ≡ Scale.educationalOutcomeTransformation

    representationReceipt : Scale.AxisVisibilityReceipt source
    representationAxisIsCorrect :
      Scale.axis representationReceipt ≡ Scale.representationWhoMissing

    disabilityReceipt : Scale.AxisVisibilityReceipt source
    disabilityAxisIsCorrect :
      Scale.axis disabilityReceipt ≡ Scale.disabilityEffectiveAccessibility

    participantAuthorityReceipt : Scale.AxisVisibilityReceipt source
    participantAuthorityAxisIsCorrect :
      Scale.axis participantAuthorityReceipt ≡ Scale.participantVoiceAuthority

    environmentReceipt : Scale.AxisVisibilityReceipt source
    environmentAxisIsCorrect :
      Scale.axis environmentReceipt ≡ Scale.environmentalMaterialLifecycle

    externalityReceipt : Scale.AxisVisibilityReceipt source
    externalityAxisIsCorrect :
      Scale.axis externalityReceipt ≡ Scale.externalityIncidence

    politicalEconomyReceipt : Scale.AxisVisibilityReceipt source
    politicalEconomyAxisIsCorrect :
      Scale.axis politicalEconomyReceipt ≡ Scale.politicalEconomy

    socialProvisioningReceipt : Scale.AxisVisibilityReceipt source
    socialProvisioningAxisIsCorrect :
      Scale.axis socialProvisioningReceipt ≡ Scale.socialProvisioningCommunity

    durabilityReceipt : Scale.AxisVisibilityReceipt source
    durabilityAxisIsCorrect :
      Scale.axis durabilityReceipt ≡ Scale.maintenanceInstitutionalDurability

    contextReceipt : Scale.AxisVisibilityReceipt source
    contextAxisIsCorrect :
      Scale.axis contextReceipt ≡ Scale.contextTransferTimeIntergenerational

open CompleteCoreAxisCoverage public

record StandardApplicabilityDeclaration : Set where
  constructor standard-applicability-declaration
  field
    lens : Standards.StandardLens
    relationship : Standards.StandardRelationship
    reason : String

open StandardApplicabilityDeclaration public

------------------------------------------------------------------------
-- SYNTHESIS ADMISSION
--
-- Marginal score completeness is necessary but insufficient. Every admitted
-- source must also carry all seven thin audit-domain boundary receipts so the
-- hyperfabric remains connected to disability/access, who-is-missing,
-- externality, political-economy, provisioning, durability and material-
-- lifecycle semantics without importing the heavyweight producer worlds.
------------------------------------------------------------------------

record SourceAuditAdmission (source : Attr.AttributedSource) : Set where
  constructor source-audit-admission
  field
    claimCeilingReading : String
    completeCoreCoverage : CompleteCoreAxisCoverage source
    completeDomainBoundaryCoverage :
      DomainBoundary.CompleteDomainBoundaryCoverage source
    hyperfabric : Hyperfabric.SourceAuditHyperfabric source
    standardsApplicability : List StandardApplicabilityDeclaration
    standardsApplicabilityDeclared : Bool
    standardsApplicabilityDeclaredIsTrue : standardsApplicabilityDeclared ≡ true
    requiredIntersectionsChecked : Bool
    requiredIntersectionsCheckedIsTrue : requiredIntersectionsChecked ≡ true
    tensionsPreservedWhenPresent : Bool
    tensionsPreservedWhenPresentIsTrue : tensionsPreservedWhenPresent ≡ true
    provenanceReceipt : Snowball.SourceRoleSnowballReceipt source
    wrongTypePromotionsBlocked : Bool
    wrongTypePromotionsBlockedIsTrue : wrongTypePromotionsBlocked ≡ true
    admissionAdmissibleForSynthesis : Bool
    admissionAdmissibleForSynthesisIsTrue : admissionAdmissibleForSynthesis ≡ true
    scoringProtocolVersion : String

open SourceAuditAdmission public

mkSourceAuditAdmission :
  (source : Attr.AttributedSource) →
  String →
  CompleteCoreAxisCoverage source →
  DomainBoundary.CompleteDomainBoundaryCoverage source →
  Hyperfabric.SourceAuditHyperfabric source →
  List StandardApplicabilityDeclaration →
  String →
  SourceAuditAdmission source
mkSourceAuditAdmission source ceiling coverage domainCoverage hyperfabric standards version =
  source-audit-admission
    ceiling
    coverage
    domainCoverage
    hyperfabric
    standards
    true refl
    true refl
    true refl
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    true refl
    true refl
    version

------------------------------------------------------------------------
-- Admission is a completeness/admissibility gate, not truth or quality.
------------------------------------------------------------------------

data AuthoritativeGrandTotalExists : Set where
data UnscoredSourceEntersSynthesis : Set where
data AuditAdmissionCreatesClaimAuthority : Set where
data AuditAdmissionRaisesClaimCeiling : Set where
data CompleteCoreCoverageCreatesIntersectionalAdequacy : Set where
data DomainBoundaryCoverageImportsProducerWorld : Set where

authoritativeGrandTotalDoesNotExist : AuthoritativeGrandTotalExists → ⊥
authoritativeGrandTotalDoesNotExist ()

unscoredSourceDoesNotEnterSynthesis : UnscoredSourceEntersSynthesis → ⊥
unscoredSourceDoesNotEnterSynthesis ()

auditAdmissionDoesNotCreateClaimAuthority : AuditAdmissionCreatesClaimAuthority → ⊥
auditAdmissionDoesNotCreateClaimAuthority ()

auditAdmissionDoesNotRaiseClaimCeiling : AuditAdmissionRaisesClaimCeiling → ⊥
auditAdmissionDoesNotRaiseClaimCeiling ()

completeCoreCoverageDoesNotCreateIntersectionalAdequacy :
  CompleteCoreCoverageCreatesIntersectionalAdequacy → ⊥
completeCoreCoverageDoesNotCreateIntersectionalAdequacy ()

domainBoundaryCoverageDoesNotImportProducerWorld :
  DomainBoundaryCoverageImportsProducerWorld → ⊥
domainBoundaryCoverageDoesNotImportProducerWorld ()

record SourceAuditAdmissionBoundary : Set where
  constructor source-audit-admission-boundary
  field
    everyAdmittedSourceRequiresCoreCoverage : Bool
    everyAdmittedSourceRequiresCoreCoverageIsTrue :
      everyAdmittedSourceRequiresCoreCoverage ≡ true
    everyAdmittedSourceRequiresDomainBoundaryCoverage : Bool
    everyAdmittedSourceRequiresDomainBoundaryCoverageIsTrue :
      everyAdmittedSourceRequiresDomainBoundaryCoverage ≡ true
    zeroScoresMayStillBeAdmitted : Bool
    zeroScoresMayStillBeAdmittedIsTrue : zeroScoresMayStillBeAdmitted ≡ true
    noAuthoritativeGrandTotal : Bool
    noAuthoritativeGrandTotalIsTrue : noAuthoritativeGrandTotal ≡ true
    admissionEqualsClaimAuthority : Bool
    admissionEqualsClaimAuthorityIsFalse : admissionEqualsClaimAuthority ≡ false
    childSourceIdentityWeldedByType : Bool
    childSourceIdentityWeldedByTypeIsTrue : childSourceIdentityWeldedByType ≡ true
    boundaryReceiptsImportHeavyweightProducerWorlds : Bool
    boundaryReceiptsImportHeavyweightProducerWorldsIsFalse :
      boundaryReceiptsImportHeavyweightProducerWorlds ≡ false

open SourceAuditAdmissionBoundary public

canonicalSourceAuditAdmissionBoundary : SourceAuditAdmissionBoundary
canonicalSourceAuditAdmissionBoundary = source-audit-admission-boundary
  true refl
  true refl
  true refl
  true refl
  false refl
  true refl
  false refl
