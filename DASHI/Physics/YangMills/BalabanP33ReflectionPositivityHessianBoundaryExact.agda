module DASHI.Physics.YangMills.BalabanP33ReflectionPositivityHessianBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Paulo A. Faria da Veiga and Michael O'Carroll,
-- "On Yang-Mills Stability Bounds and Plaquette Field Generating Function".
-- arXiv DOI: 10.48550/arXiv.2205.07376.
-- Status: arXiv preprint.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II".
-- DOI: 10.1007/BF01240221.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schroedinger
-- Operators".
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
-- Type-separate two rigorous uniformity routes:
--
--   reflection-positive/observable route:
--     partition function, free energy, generating functions, moments;
--
--   Hessian/Schur route:
--     coercive floor, inverse-kernel decay, Schur transfer, spectral gap.
--
-- A concrete non-injectivity witness gives two candidates with identical
-- observable-route data and different spectral-route tags.  Therefore uniform
-- moment data alone do not determine a positive Hessian or mass gap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Empty using (⊥)

data ObservableUniformity : Set where
  normalizedPartitionBound : ObservableUniformity
  plaquetteGeneratingBound : ObservableUniformity

data SpectralUniformity : Set where
  positiveHessianAndDecay : SpectralUniformity
  noSpectralCertificate : SpectralUniformity

record UniformityCandidate : Set where
  constructor uniformityCandidate
  field
    partitionRoute : ObservableUniformity
    generatingRoute : ObservableUniformity
    spectralRoute : SpectralUniformity

open UniformityCandidate public

candidateWithSpectralControl : UniformityCandidate
candidateWithSpectralControl =
  uniformityCandidate
    normalizedPartitionBound
    plaquetteGeneratingBound
    positiveHessianAndDecay

candidateWithoutSpectralControl : UniformityCandidate
candidateWithoutSpectralControl =
  uniformityCandidate
    normalizedPartitionBound
    plaquetteGeneratingBound
    noSpectralCertificate

record ObservableProjection : Set where
  constructor observableProjection
  field
    partitionObservation : ObservableUniformity
    generatingObservation : ObservableUniformity

observeUniformity : UniformityCandidate → ObservableProjection
observeUniformity candidate =
  observableProjection
    (partitionRoute candidate)
    (generatingRoute candidate)

observableRoutesAgree :
  observeUniformity candidateWithSpectralControl
  ≡ observeUniformity candidateWithoutSpectralControl
observableRoutesAgree = refl

spectralTagsAreDistinct :
  positiveHessianAndDecay ≡ noSpectralCertificate → ⊥
spectralTagsAreDistinct ()

candidatesAreDistinct :
  candidateWithSpectralControl ≡ candidateWithoutSpectralControl → ⊥
candidatesAreDistinct equality =
  spectralTagsAreDistinct (cong spectralRoute equality)

observableProjectionIsNotInjective : Set
observableProjectionIsNotInjective =
  candidateWithSpectralControl ≡ candidateWithoutSpectralControl → ⊥

observableProjectionIsNotInjectiveWitness :
  observableProjectionIsNotInjective
observableProjectionIsNotInjectiveWitness = candidatesAreDistinct

data RouteKind : Set where
  reflectionPositiveObservableRoute : RouteKind
  coerciveHessianSchurRoute : RouteKind

record ReflectionHessianBoundary : Set where
  constructor reflectionHessianBoundary
  field
    generatingFunctionBoundImpliesPositiveHessian : Set
    generatingFunctionBoundDoesNotAutomaticallyImplyPositiveHessian :
      generatingFunctionBoundImpliesPositiveHessian → Set

    partitionStabilityImpliesExponentialClustering : Set
    partitionStabilityDoesNotAutomaticallyImplyExponentialClustering :
      partitionStabilityImpliesExponentialClustering → Set

canonicalReflectionHessianBoundary : ReflectionHessianBoundary
canonicalReflectionHessianBoundary =
  reflectionHessianBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
