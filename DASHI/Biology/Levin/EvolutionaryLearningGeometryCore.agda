module DASHI.Biology.Levin.EvolutionaryLearningGeometryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.GenotypePhenotypeGeometry as Geometry
import DASHI.Biology.Levin.CovarianceMetricBridge as Covariance
import DASHI.Biology.Levin.PriceLandeLearningBridge as Learning
import DASHI.Biology.Levin.MultilevelEvolutionCoupling as Coupling

------------------------------------------------------------------------
-- Candidate integration facade for geometric evolutionary learning.

record EvolutionaryLearningGeometryCore : Set where
  field
    geometryBoundary : Geometry.GeometryBoundary
    geometryBoundaryIsCanonical :
      geometryBoundary ≡ Geometry.canonicalGeometryBoundary

    covarianceMetricBoundary : Covariance.CovarianceMetricBoundary
    covarianceMetricBoundaryIsCanonical :
      covarianceMetricBoundary ≡ Covariance.canonicalCovarianceMetricBoundary

    priceLandeBoundary : Learning.PriceLandeBoundary
    priceLandeBoundaryIsCanonical :
      priceLandeBoundary ≡ Learning.canonicalPriceLandeBoundary

    multilevelCouplingBoundary : Coupling.MultilevelCouplingBoundary
    multilevelCouplingBoundaryIsCanonical :
      multilevelCouplingBoundary ≡ Coupling.canonicalMultilevelCouplingBoundary

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    noExactEvolutionEqualsLearningPromotion : Bool
    noExactEvolutionEqualsLearningPromotionIsFalse :
      noExactEvolutionEqualsLearningPromotion ≡ false

    noCanonicalEmbeddingPromotion : Bool
    noCanonicalEmbeddingPromotionIsFalse :
      noCanonicalEmbeddingPromotion ≡ false

    noUniversalMaximumEntropyPromotion : Bool
    noUniversalMaximumEntropyPromotionIsFalse :
      noUniversalMaximumEntropyPromotion ≡ false

    formalisationReading : String

open EvolutionaryLearningGeometryCore public

canonicalEvolutionaryLearningGeometryCore : EvolutionaryLearningGeometryCore
canonicalEvolutionaryLearningGeometryCore = record
  { geometryBoundary = Geometry.canonicalGeometryBoundary
  ; geometryBoundaryIsCanonical = refl
  ; covarianceMetricBoundary = Covariance.canonicalCovarianceMetricBoundary
  ; covarianceMetricBoundaryIsCanonical = refl
  ; priceLandeBoundary = Learning.canonicalPriceLandeBoundary
  ; priceLandeBoundaryIsCanonical = refl
  ; multilevelCouplingBoundary = Coupling.canonicalMultilevelCouplingBoundary
  ; multilevelCouplingBoundaryIsCanonical = refl
  ; candidateOnly = true
  ; candidateOnlyIsTrue = refl
  ; noExactEvolutionEqualsLearningPromotion = false
  ; noExactEvolutionEqualsLearningPromotionIsFalse = refl
  ; noCanonicalEmbeddingPromotion = false
  ; noCanonicalEmbeddingPromotionIsFalse = refl
  ; noUniversalMaximumEntropyPromotion = false
  ; noUniversalMaximumEntropyPromotionIsFalse = refl
  ; formalisationReading =
      "Evolutionary change is represented on typed genotype and phenotype carriers; covariance-to-metric and Price-to-Lande-to-natural-gradient steps remain assumption-indexed approximations with explicit cross-level coupling remainders"
  }

canonicalEvolutionaryLearningGeometryModules : List String
canonicalEvolutionaryLearningGeometryModules =
  "DASHI.Biology.Levin.GenotypePhenotypeGeometry"
  ∷ "DASHI.Biology.Levin.CovarianceMetricBridge"
  ∷ "DASHI.Biology.Levin.PriceLandeLearningBridge"
  ∷ "DASHI.Biology.Levin.MultilevelEvolutionCoupling"
  ∷ "DASHI.Biology.Levin.EvolutionaryLearningGeometryCore"
  ∷ []
