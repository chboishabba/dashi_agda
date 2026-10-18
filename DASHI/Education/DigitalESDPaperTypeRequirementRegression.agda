module DASHI.Education.DigitalESDPaperTypeRequirementRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Empty using (⊥)

import DASHI.Core.RequirementProducerSchedulerExact as Scheduler
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper

currentPaperTypeRegression :
  Paper.currentPaperType ≡ Paper.integrativeConceptualReview
currentPaperTypeRegression = refl

conceptualSearchRequiredRegression :
  Paper.requiredFor Paper.integrativeConceptualReview Paper.transparentStructuredSearch
  ≡ true
conceptualSearchRequiredRegression = refl

conceptualEvidenceScopeRequiredRegression :
  Paper.requiredFor Paper.integrativeConceptualReview Paper.sourceRoleScopeSynthesis
  ≡ true
conceptualEvidenceScopeRequiredRegression = refl

conceptualLifecycleSynthesisRequiredRegression :
  Paper.requiredFor Paper.integrativeConceptualReview Paper.lifecycleEvidenceSynthesis
  ≡ true
conceptualLifecycleSynthesisRequiredRegression = refl

conceptualSameObjectLCANotRequiredRegression :
  Paper.requiredFor Paper.integrativeConceptualReview Paper.sameObjectInterventionLCA
  ≡ false
conceptualSameObjectLCANotRequiredRegression = refl

systematicProtocolRequiredRegression :
  Paper.requiredFor Paper.systematicReview Paper.reproducibleSystematicProtocol
  ≡ true
systematicProtocolRequiredRegression = refl

systematicScreeningRequiredRegression :
  Paper.requiredFor Paper.systematicReview Paper.screeningExtractionAuditTrail
  ≡ true
systematicScreeningRequiredRegression = refl

empiricalSameObjectLCARequiredRegression :
  Paper.requiredFor Paper.empiricalDigitalESDIntervention Paper.sameObjectInterventionLCA
  ≡ true
empiricalSameObjectLCARequiredRegression = refl

currentMissingSearchReceiptRegression :
  Scheduler.MissingFor
    Paper.digitalESDPaperRequirementSystem
    Paper.integrativeConceptualReview
    Paper.transparentStructuredSearch
currentMissingSearchReceiptRegression = refl , refl

systematicLabelWithoutProtocolRegression :
  Paper.SystematicReviewLabelWithoutProtocol → ⊥
systematicLabelWithoutProtocolRegression =
  Paper.systematicReviewLabelRequiresProtocol

conceptualReviewDoesNotRequireInterventionLCARegression :
  Paper.ConceptualReviewRequiresSameObjectInterventionLCA → ⊥
conceptualReviewDoesNotRequireInterventionLCARegression =
  Paper.conceptualReviewDoesNotRequireSameObjectInterventionLCA
