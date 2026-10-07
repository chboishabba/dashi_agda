{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PublishedEuclideanBackgroundCovarianceTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.CMP119CosmologyP1PublishedEuclideanBackgroundCovarianceExact as P1

noFreshCovarianceProof :
  P1.publishedPotentialCovarianceNeedsFreshProof ≡ false
noFreshCovarianceProof = refl

sameObjectWeldRemains :
  P1.remainingS1WorkIsSameObjectBackgroundAndTangentIdentification ≡ true
sameObjectWeldRemains = refl

tenDirectionsRemain :
  P1.remainingS1WorkIncludesTenMetricDirectionsInPublishedBAction ≡ true
tenDirectionsRemain = refl
