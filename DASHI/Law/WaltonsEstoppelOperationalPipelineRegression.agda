module DASHI.Law.WaltonsEstoppelOperationalPipelineRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Law.WaltonsEstoppelOperationalPipelineExact as Pipeline

boundaryExists : Set
boundaryExists = Pipeline.WaltonsOperationalPipelineBoundary

boundaryPaid : boundaryExists
boundaryPaid = Pipeline.canonicalWaltonsOperationalPipelineBoundary

paragraphReviewStillHumanGated :
  Pipeline.executionClass Pipeline.reviewWaltonsParagraphs
    ≡ Pipeline.humanLegalReviewRequired
paragraphReviewStillHumanGated =
  Pipeline.reviewWaltonsIsHumanGate

citedByStillExternalProviderGated :
  Pipeline.executionClass Pipeline.discoverLaterTreatmentCitedBy
    ≡ Pipeline.externalProviderRequired
citedByStillExternalProviderGated =
  Pipeline.citedByIsExternalProviderGate

textSearchStillCannotSubstituteForCitedBy :
  Pipeline.MissingProviderMayBeReplacedByTextSearch → ⊥
textSearchStillCannotSubstituteForCitedBy =
  Pipeline.textSearchCannotSubstituteForCitedBy
