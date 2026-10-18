module DASHI.Education.DigitalESDFirstRetainedStudyParseRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDFirstRetainedStudyParseExact as First

firstStudyIsEJ1083370 :
  First.sourceIdentityReference First.ej1083370Receipt
  ≡ "ERIC:EJ1083370"
firstStudyIsEJ1083370 = refl

firstStudyPageCountIsThirty :
  First.pageCount First.ej1083370Receipt ≡ 30
firstStudyPageCountIsThirty = refl

firstStudyNodeCountIs1298 :
  First.documentNodeCount First.ej1083370Receipt ≡ 1298
firstStudyNodeCountIs1298 = refl

firstStudyFacetCountIsThirteen :
  First.studyFacetCount First.ej1083370Receipt ≡ 13
firstStudyFacetCountIsThirteen = refl

facetCandidatesCannotCreateStudyTruth :
  First.StudyFacetCandidateCreatesStudyTruth → ⊥
facetCandidatesCannotCreateStudyTruth =
  First.studyFacetCandidateDoesNotCreateStudyTruth

facetCandidatesCannotCreateAdmission :
  First.StudyFacetCandidateCreatesSourceAuditAdmission → ⊥
facetCandidatesCannotCreateAdmission =
  First.studyFacetCandidateDoesNotCreateSourceAuditAdmission

parserReceiptCannotPayCoordinates :
  First.FirstStudyParseCreatesExtractionPayment → ⊥
parserReceiptCannotPayCoordinates =
  First.firstStudyParseDoesNotCreateExtractionPayment
