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

existingApplicabilityCompilerRetained :
  Brighton.BrightonS185RegressionBoundary.existingApplicabilityCompilerRetained
    Brighton.canonicalBrightonS185RegressionBoundary ≡ true
existingApplicabilityCompilerRetained = refl

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

healthContextDoesNotCreateMedicalCausation :
  Brighton.BrightonS185RegressionBoundary.healthContextCreatesMedicalCausation
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
healthContextDoesNotCreateMedicalCausation = refl

oneEpisodeDoesNotCreateSystemicWrongdoing :
  Brighton.BrightonS185RegressionBoundary.oneEpisodeCreatesSystemicWrongdoing
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
oneEpisodeDoesNotCreateSystemicWrongdoing = refl

applicabilityDoesNotCreateLiability :
  Brighton.BrightonS185RegressionBoundary.applicabilityCreatesLiability
    Brighton.canonicalBrightonS185RegressionBoundary ≡ false
applicabilityDoesNotCreateLiability = refl
