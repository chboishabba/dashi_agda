module DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapExact as Literature

observerFamilyRegression :
  Literature.canonicalLiteratureObserverFamily
  ≡ Literature.technologyAsPedagogicalTool
  ∷ Literature.technologyAsSustainabilityObject
  ∷ Literature.sustainabilityInsideComputingEducation
  ∷ Literature.educationalDigitalInfrastructureFootprint
  ∷ []
observerFamilyRegression = refl

pedagogicalToolReviewPaidRegression :
  Literature.DigitalESDLiteratureMap.digitalToolEnvironmentalEducationReviewPaid
    Literature.canonicalDigitalESDLiteratureMap
  ≡ true
pedagogicalToolReviewPaidRegression = refl

compulsoryEducationMapPaidRegression :
  Literature.DigitalESDLiteratureMap.compulsoryEducationScopingReviewPaid
    Literature.canonicalDigitalESDLiteratureMap
  ≡ true
compulsoryEducationMapPaidRegression = refl

computingEducationMapPaidRegression :
  Literature.DigitalESDLiteratureMap.computingEducationSystematicReviewPaid
    Literature.canonicalDigitalESDLiteratureMap
  ≡ true
computingEducationMapPaidRegression = refl

genAIEnvironmentalMapPaidRegression :
  Literature.DigitalESDLiteratureMap.genAIEducationEnvironmentalReviewPaid
    Literature.canonicalDigitalESDLiteratureMap
  ≡ true
genAIEnvironmentalMapPaidRegression = refl

candidateNotIncludedRegression :
  Literature.DigitalESDLiteratureMap.acquiredSourcesAreIncludedStudies
    Literature.canonicalDigitalESDLiteratureMap
  ≡ false
candidateNotIncludedRegression = refl

toolDoesNotPromoteSustainableTechnologyRegression :
  Literature.TechnologyUsedForSustainabilityTeachingProvesSustainableTechnology → ⊥
toolDoesNotPromoteSustainableTechnologyRegression =
  Literature.technologyUsedForSustainabilityTeachingDoesNotProveSustainableTechnology

populationTransferRegression :
  Literature.CompulsoryEducationEvidenceAutomaticallyTransfersToHigherEducation → ⊥
populationTransferRegression =
  Literature.compulsoryEducationEvidenceDoesNotAutomaticallyTransferToHigherEducation

reviewDoesNotCreatePaperInclusionRegression :
  Literature.SourceAcquisitionCreatesPaperInclusion → ⊥
reviewDoesNotCreatePaperInclusionRegression =
  Literature.sourceAcquisitionDoesNotCreatePaperInclusion
