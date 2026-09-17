module DASHI.Education.DigitalESDAuditDomainBoundaryReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale

------------------------------------------------------------------------
-- THIN DOMAIN-BOUNDARY RECEIPTS
--
-- This module is intentionally dependency-light. It names the audit-facing
-- semantic contract exported by heavyweight Digital-ESD owners without
-- importing those owners transitively into the source-audit hyperfabric.
--
-- A receipt records the source-relative applicability of a domain boundary;
-- it does not reproduce the donor implementation, import its empirical claims,
-- or manufacture proof/authority from the producer-module label.
------------------------------------------------------------------------

data DomainBoundaryFamily : Set where
  disabilityAccessibilityBoundary : DomainBoundaryFamily
  whoMissingAbsenceBoundary : DomainBoundaryFamily
  externalityIncidenceBoundary : DomainBoundaryFamily
  politicalEconomyBoundary : DomainBoundaryFamily
  socialProvisioningBoundary : DomainBoundaryFamily
  institutionalDurabilityBoundary : DomainBoundaryFamily
  materialLifecycleBoundary : DomainBoundaryFamily

data BoundaryApplicability : Set where
  applicable : String → BoundaryApplicability
  notApplicable : String → BoundaryApplicability

record DomainBoundaryReceipt (source : Attr.AttributedSource) : Set where
  constructor domain-boundary-receipt
  field
    family : DomainBoundaryFamily
    producerModule : String
    producerContract : String
    consumerAxis : Scale.AuditAxis
    applicability : BoundaryApplicability
    sourceSpecificReason : String
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    receiptImportsProducerWorld : Bool
    receiptImportsProducerWorldIsFalse : receiptImportsProducerWorld ≡ false
    receiptCreatesEmpiricalEvidence : Bool
    receiptCreatesEmpiricalEvidenceIsFalse : receiptCreatesEmpiricalEvidence ≡ false
    receiptCreatesAuthority : Bool
    receiptCreatesAuthorityIsFalse : receiptCreatesAuthority ≡ false

open DomainBoundaryReceipt public

mkDomainBoundaryReceipt :
  (source : Attr.AttributedSource) →
  DomainBoundaryFamily →
  String →
  String →
  Scale.AuditAxis →
  BoundaryApplicability →
  String →
  DomainBoundaryReceipt source
mkDomainBoundaryReceipt source family producerModule producerContract axis applicability reason =
  domain-boundary-receipt
    family
    producerModule
    producerContract
    axis
    applicability
    reason
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Complete domain-boundary coverage required by SourceAuditAdmission.
--
-- Applicability and visibility are intentionally distinct. A boundary may be
-- not applicable while the corresponding mandatory 0--5 audit axis still has
-- a legitimate score (often 0 because the source does not address it).
------------------------------------------------------------------------

record CompleteDomainBoundaryCoverage (source : Attr.AttributedSource) : Set where
  constructor complete-domain-boundary-coverage
  field
    disabilityReceipt : DomainBoundaryReceipt source
    disabilityFamilyIsCorrect :
      family disabilityReceipt ≡ disabilityAccessibilityBoundary

    absenceReceipt : DomainBoundaryReceipt source
    absenceFamilyIsCorrect :
      family absenceReceipt ≡ whoMissingAbsenceBoundary

    externalityReceipt : DomainBoundaryReceipt source
    externalityFamilyIsCorrect :
      family externalityReceipt ≡ externalityIncidenceBoundary

    politicalEconomyReceipt : DomainBoundaryReceipt source
    politicalEconomyFamilyIsCorrect :
      family politicalEconomyReceipt ≡ politicalEconomyBoundary

    socialProvisioningReceipt : DomainBoundaryReceipt source
    socialProvisioningFamilyIsCorrect :
      family socialProvisioningReceipt ≡ socialProvisioningBoundary

    durabilityReceipt : DomainBoundaryReceipt source
    durabilityFamilyIsCorrect :
      family durabilityReceipt ≡ institutionalDurabilityBoundary

    materialLifecycleReceipt : DomainBoundaryReceipt source
    materialLifecycleFamilyIsCorrect :
      family materialLifecycleReceipt ≡ materialLifecycleBoundary

open CompleteDomainBoundaryCoverage public

------------------------------------------------------------------------
-- Canonical producer coordinates.
--
-- Strings are provenance coordinates naming the existing producer surfaces;
-- they are not a substitute for executing/typechecking those producer owners.
------------------------------------------------------------------------

disabilityProducerModule : String
disabilityProducerModule = "DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact"

disabilityProducerContract : String
disabilityProducerContract = "canonicalDisabilityDigitalESDBoundary"

absenceProducerModule : String
absenceProducerModule = "DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact"

absenceProducerContract : String
absenceProducerContract = "absenceAuditQuestionCount / study absence audit surface"

externalityProducerModule : String
externalityProducerModule = "DASHI.Education.DigitalESDExternalityIncidenceAuditExact"

externalityProducerContract : String
externalityProducerContract = "canonicalExternalityIncidenceBoundary"

politicalEconomyProducerModule : String
politicalEconomyProducerModule = "DASHI.Education.DigitalESDPoliticalEconomyProvisioningExact"

politicalEconomyProducerContract : String
politicalEconomyProducerContract = "canonicalDigitalESDPoliticalEconomyBoundary"

socialProvisioningProducerModule : String
socialProvisioningProducerModule = "DASHI.Education.DigitalESDSocialProvisioningContinuityExact"

socialProvisioningProducerContract : String
socialProvisioningProducerContract = "canonicalSocialProvisioningBoundary"

durabilityProducerModule : String
durabilityProducerModule = "DASHI.Education.DigitalESDInstitutionalDurabilityMaintenanceExact"

durabilityProducerContract : String
durabilityProducerContract = "canonicalInstitutionalDurabilityBoundary"

materialLifecycleProducerModule : String
materialLifecycleProducerModule = "DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact"

materialLifecycleProducerContract : String
materialLifecycleProducerContract = "material/environmental substrate audit surface"

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data DomainBoundaryReceiptCreatesEmpiricalEvidence : Set where
data DomainBoundaryReceiptCreatesAuthority : Set where
data ProducerModuleLabelImportsProducerWorld : Set where
data NotApplicableEqualsScoreZero : Set where

domainBoundaryReceiptDoesNotCreateEmpiricalEvidence :
  DomainBoundaryReceiptCreatesEmpiricalEvidence → ⊥
domainBoundaryReceiptDoesNotCreateEmpiricalEvidence ()

domainBoundaryReceiptDoesNotCreateAuthority :
  DomainBoundaryReceiptCreatesAuthority → ⊥
domainBoundaryReceiptDoesNotCreateAuthority ()

producerModuleLabelDoesNotImportProducerWorld :
  ProducerModuleLabelImportsProducerWorld → ⊥
producerModuleLabelDoesNotImportProducerWorld ()

notApplicableIsNotScoreZero : NotApplicableEqualsScoreZero → ⊥
notApplicableIsNotScoreZero ()

record DomainBoundaryCoverageBoundary : Set where
  constructor domain-boundary-coverage-boundary
  field
    allSevenFamiliesRequired : Bool
    allSevenFamiliesRequiredIsTrue : allSevenFamiliesRequired ≡ true
    heavyweightOwnersImportedByAudit : Bool
    heavyweightOwnersImportedByAuditIsFalse : heavyweightOwnersImportedByAudit ≡ false
    notApplicableDistinctFromZero : Bool
    notApplicableDistinctFromZeroIsTrue : notApplicableDistinctFromZero ≡ true
    semanticCrossPollinationEqualsTransitiveImport : Bool
    semanticCrossPollinationEqualsTransitiveImportIsFalse :
      semanticCrossPollinationEqualsTransitiveImport ≡ false

open DomainBoundaryCoverageBoundary public

canonicalDomainBoundaryCoverageBoundary : DomainBoundaryCoverageBoundary
canonicalDomainBoundaryCoverageBoundary =
  domain-boundary-coverage-boundary
    true refl
    false refl
    true refl
    false refl
