module DASHI.Law.TraumaNarrativeEvidenceBoundaryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.TraumaNarrativeEvidenceBoundaryExact as Trauma

parentFragmentationReusedRegression :
  Trauma.parentFragmentationReused Trauma.canonicalTraumaNarrativeEvidenceBoundary
  ≡ true
parentFragmentationReusedRegression = refl

fragmentationEvidenceInconclusiveRegression :
  Trauma.reviewEvidenceForPTSDNarrativeFragmentationInconclusive
    Trauma.canonicalTraumaNarrativeEvidenceBoundary
  ≡ true
fragmentationEvidenceInconclusiveRegression = refl

heterogeneousReviewRegression :
  Trauma.laterReviewNarrativeFragmentationResultsHeterogeneous
    Trauma.canonicalTraumaNarrativeEvidenceBoundary
  ≡ true
heterogeneousReviewRegression = refl

traumaAutomaticallyFragmentedRegression :
  Trauma.traumaAutomaticallyFragmentedNarrative
    Trauma.canonicalTraumaNarrativeEvidenceBoundary
  ≡ false
traumaAutomaticallyFragmentedRegression = refl

fragmentationAutomaticallyTraumaRegression :
  Trauma.fragmentedNarrativeAutomaticallyTrauma
    Trauma.canonicalTraumaNarrativeEvidenceBoundary
  ≡ false
fragmentationAutomaticallyTraumaRegression = refl

coherenceTruthRegression :
  Trauma.narrativeCoherenceAutomaticallyTruth
    Trauma.canonicalTraumaNarrativeEvidenceBoundary
  ≡ false
coherenceTruthRegression = refl

reviewCaseFindingRegression :
  Trauma.reviewScholarshipAutomaticallyCaseSpecificFinding
    Trauma.canonicalTraumaNarrativeEvidenceBoundary
  ≡ false
reviewCaseFindingRegression = refl
