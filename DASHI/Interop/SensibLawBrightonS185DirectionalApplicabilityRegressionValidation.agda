module DASHI.Interop.SensibLawBrightonS185DirectionalApplicabilityRegressionValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawBrightonS185DirectionalApplicabilityRegressionExact as Brighton

oneEpisodeOnly :
  Brighton.BrightonS185RegressionBoundary.oneEpisodeOnly
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
oneEpisodeOnly = refl

form11IsMatterEvidenceCarrier :
  Brighton.BrightonS185RegressionBoundary.form11IsMatterEvidenceCarrier
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
form11IsMatterEvidenceCarrier = refl

exactSourceResidualRequired :
  Brighton.BrightonS185RegressionBoundary.exactSourceResidualRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
exactSourceResidualRequired = refl

exactTargetClaimBindingRequired :
  Brighton.BrightonS185RegressionBoundary.exactTargetClaimBindingRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
exactTargetClaimBindingRequired = refl

exactSourceArtifactReceiptRequired :
  Brighton.BrightonS185RegressionBoundary.exactSourceArtifactReceiptRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
exactSourceArtifactReceiptRequired = refl

supportedDispositionRequired :
  Brighton.BrightonS185RegressionBoundary.supportedDispositionRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
supportedDispositionRequired = refl

canonicalSourceAdmissionRequired :
  Brighton.BrightonS185RegressionBoundary.canonicalSourceAdmissionRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
canonicalSourceAdmissionRequired = refl

positiveSupportPaidByCanonicalAdmission :
  Brighton.BrightonS185RegressionBoundary.positiveSupportPaidByCanonicalAdmission
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
positiveSupportPaidByCanonicalAdmission = refl

positiveTritPaidByCanonicalAdmission :
  Brighton.BrightonS185RegressionBoundary.positiveTritPaidByCanonicalAdmission
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
positiveTritPaidByCanonicalAdmission = refl

section185IsIndependentLegalAuthority :
  Brighton.BrightonS185RegressionBoundary.section185IsIndependentLegalAuthority
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
section185IsIndependentLegalAuthority = refl

positiveSourceSupportRequiredBeforeBridge :
  Brighton.BrightonS185RegressionBoundary.positiveSourceSupportRequiredBeforeBridge
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
positiveSourceSupportRequiredBeforeBridge = refl

sameMatterPropositionWeldRequired :
  Brighton.BrightonS185RegressionBoundary.sameMatterPropositionWeldRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
sameMatterPropositionWeldRequired = refl

sameEvidenceCarrierWeldRequired :
  Brighton.BrightonS185RegressionBoundary.sameEvidenceCarrierWeldRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
sameEvidenceCarrierWeldRequired = refl

sameSection185AuthorityWeldRequired :
  Brighton.BrightonS185RegressionBoundary.sameSection185AuthorityWeldRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
sameSection185AuthorityWeldRequired = refl

exactHistoricalAuthorityReceiptRequired :
  Brighton.BrightonS185RegressionBoundary.exactHistoricalAuthorityReceiptRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
exactHistoricalAuthorityReceiptRequired = refl

exactJurisdictionReceiptRequired :
  Brighton.BrightonS185RegressionBoundary.exactJurisdictionReceiptRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
exactJurisdictionReceiptRequired = refl

exactTemporalScopeReceiptRequired :
  Brighton.BrightonS185RegressionBoundary.exactTemporalScopeReceiptRequired
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
exactTemporalScopeReceiptRequired = refl

existingApplicabilityCompilerRetained :
  Brighton.BrightonS185RegressionBoundary.existingApplicabilityCompilerRetained
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
existingApplicabilityCompilerRetained = refl

existingViolationCompilerRetained :
  Brighton.BrightonS185RegressionBoundary.existingViolationCompilerRetained
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
existingViolationCompilerRetained = refl

exactApplicabilityReceiptReusedByViolation :
  Brighton.BrightonS185RegressionBoundary.exactApplicabilityReceiptReusedByViolation
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
exactApplicabilityReceiptReusedByViolation = refl

form11DoesNotCreateBreach :
  Brighton.BrightonS185RegressionBoundary.form11AssertionCreatesBreach
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
form11DoesNotCreateBreach = refl

positiveSupportDoesNotCreateViolation :
  Brighton.BrightonS185RegressionBoundary.positiveSupportCreatesViolation
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
positiveSupportDoesNotCreateViolation = refl

legalAuthorityDoesNotCreateMatterFact :
  Brighton.BrightonS185RegressionBoundary.legalAuthorityCreatesMatterFact
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
legalAuthorityDoesNotCreateMatterFact = refl

nearbyCompilationDoesNotCreateHistoricalAuthority :
  Brighton.BrightonS185RegressionBoundary.nearbyCompilationCreatesHistoricalAuthority
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
nearbyCompilationDoesNotCreateHistoricalAuthority = refl

unweldedSection185LabelDoesNotAuthorizeApplicability :
  Brighton.BrightonS185RegressionBoundary.unweldedSection185LabelAuthorizesApplicability
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
unweldedSection185LabelDoesNotAuthorizeApplicability = refl

healthContextDoesNotCreateMedicalCausation :
  Brighton.BrightonS185RegressionBoundary.healthContextCreatesMedicalCausation
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
healthContextDoesNotCreateMedicalCausation = refl

oneEpisodeDoesNotCreateSystemicWrongdoing :
  Brighton.BrightonS185RegressionBoundary.oneEpisodeCreatesSystemicWrongdoing
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
oneEpisodeDoesNotCreateSystemicWrongdoing = refl

applicabilityDoesNotCreateViolation :
  Brighton.BrightonS185RegressionBoundary.applicabilityCreatesViolation
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
applicabilityDoesNotCreateViolation = refl

violationDoesNotCreateLiability :
  Brighton.BrightonS185RegressionBoundary.violationCreatesLiability
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
violationDoesNotCreateLiability = refl
