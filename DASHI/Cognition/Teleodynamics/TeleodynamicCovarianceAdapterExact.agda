module DASHI.Cognition.Teleodynamics.TeleodynamicCovarianceAdapterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Information.PNFSpectralGeometry as Spectral
import DASHI.Cognition.TeleodynamicsPrincipiaTwoExact as T

------------------------------------------------------------------------
-- TELEODYNAMIC C-TENSOR -> EXISTING COVARIANCE / SPECTRAL GEOMETRY OWNER
--
-- PNFSpectralGeometry already owns activation surfaces, centering, covariance,
-- anonymous eigenspectra, cleaning, and transport.  The new teleodynamic layer
-- therefore records only the cross-observable/rate normalization adapter and
-- the authority boundary around interpretation.
------------------------------------------------------------------------

record TeleodynamicCrossCovarianceAdapter : Set where
  constructor teleodynamicCrossCovarianceAdapter
  field
    activationSurfaceLabel : String
    observableCoordinateLabel : String
    rateCoordinateLabel : String
    centeredObservableLabel : String
    centeredRateLabel : String
    crossCovarianceLabel : String
    observableVarianceLabel : String
    rateVarianceLabel : String
    normalizedCorrelationLabel : String
    nonzeroVarianceConditionLabel : String
    boundedCorrelationProofLabel : String

record TeleodynamicCovarianceBoundary : Set where
  constructor teleodynamicCovarianceBoundary
  field
    pnfSpectralGeometryOwnerReused : Bool
    covarianceEqualsNormalizedCorrelation : Bool
    normalizedCorrelationRequiresVarianceNormalization : Bool
    anonymousSpectrumCreatesSemanticLabels : Bool
    spectrumEstablishesConsciousness : Bool
    covarianceCreatesMetricOrCurvature : Bool

open TeleodynamicCovarianceBoundary public

canonicalTeleodynamicCovarianceBoundary : TeleodynamicCovarianceBoundary
canonicalTeleodynamicCovarianceBoundary =
  teleodynamicCovarianceBoundary true false true false false false

canonicalCrossCovarianceAdapter : TeleodynamicCrossCovarianceAdapter
canonicalCrossCovarianceAdapter =
  teleodynamicCrossCovarianceAdapter
    "PNFSpectralGeometry.ActivationSurface"
    "O_mu"
    "O-dot_nu"
    "delta O_mu"
    "delta O-dot_nu"
    "Cov(delta O_mu, delta O-dot_nu)"
    "Var(delta O_mu)"
    "Var(delta O-dot_nu)"
    "cross covariance / sqrt(var_mu var_dot_nu)"
    "both variances nonzero"
    "Cauchy-Schwarz / bounded-correlation obligation"

-- Existing source-facing C entries can consume an analytic normalization
-- receipt; this adapter does not replace the current CorrelationWitness until a
-- concrete real-analysis constructor is supplied.
teleodynamicCorrelationStillWitnessGated : Bool
teleodynamicCorrelationStillWitnessGated = true
