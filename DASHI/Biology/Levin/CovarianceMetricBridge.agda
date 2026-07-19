module DASHI.Biology.Levin.CovarianceMetricBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Statistics-to-geometry bridge.
--
-- Covariance and inverse metric have compatible variance, but identifying
-- them requires a modelling principle such as a local maximum-entropy family.

record CovarianceMetricBridge : Set₁ where
  field
    State       : Set
    Tangent     : Set
    Scalar      : Set
    Distribution : Set

    covariance    : Distribution → Tangent → Tangent → Scalar
    inverseMetric : State → Tangent → Tangent → Scalar

    locallyMaximumEntropy : Distribution → Bool
    covarianceNondegenerate : Distribution → Bool

    identifiesInverseMetric : Distribution → Bool

    identificationRequiresMaximumEntropy : Bool
    identificationRequiresMaximumEntropyIsTrue :
      identificationRequiresMaximumEntropy ≡ true

    covarianceTransformsContravariantly : Bool
    covarianceTransformsContravariantlyIsTrue :
      covarianceTransformsContravariantly ≡ true

    bridgeReading : String

open CovarianceMetricBridge public

record CovarianceMetricBoundary : Set where
  field
    covarianceIsNotMetricByTypeAlone : Bool
    covarianceIsNotMetricByTypeAloneIsFalse :
      covarianceIsNotMetricByTypeAlone ≡ false

    singularCovarianceDoesNotDefineFullMetric : Bool
    singularCovarianceDoesNotDefineFullMetricIsFalse :
      singularCovarianceDoesNotDefineFullMetric ≡ false

    maximumEntropyIsModelAssumption : Bool
    maximumEntropyIsModelAssumptionIsTrue :
      maximumEntropyIsModelAssumption ≡ true

canonicalCovarianceMetricBoundary : CovarianceMetricBoundary
canonicalCovarianceMetricBoundary = record
  { covarianceIsNotMetricByTypeAlone = false
  ; covarianceIsNotMetricByTypeAloneIsFalse = refl
  ; singularCovarianceDoesNotDefineFullMetric = false
  ; singularCovarianceDoesNotDefineFullMetricIsFalse = refl
  ; maximumEntropyIsModelAssumption = true
  ; maximumEntropyIsModelAssumptionIsTrue = refl
  }
