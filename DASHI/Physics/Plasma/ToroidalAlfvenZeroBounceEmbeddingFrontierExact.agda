module DASHI.Physics.Plasma.ToroidalAlfvenZeroBounceEmbeddingFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.CircularAlfvenZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.DynamicZeroBounceAdmissibilityExact as Dynamic
import DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact as Invariant
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- TOROIDAL EMBEDDING FRONTIER
--
-- The circular Alfven seed pays literal local mirror elimination in ideal MHD.
-- The remaining hard obligations are toroidal: curvature / grad-B drift,
-- finite orbit width, field-line closure, finite-beta equilibrium, actuator
-- synthesis and induced-E/control-power constraints.
------------------------------------------------------------------------

record ToroidalAlfvenZeroBounceCandidate
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor toroidal-alfven-zero-bounce-candidate
  field
    localSeed : Seed.CircularAlfvenZeroBounceSeed population
    dynamicAdmissibility : Dynamic.DynamicDetrappingAdmissibility population

    toroidalEmbeddingReceipt : Set
    orientableNestedFluxSurfaceReceipt : Set
    divergenceFreeGlobalFieldReceipt : Set
    finiteBetaForceBalanceReceipt : Set
    fieldLineClosureOrTransformReceipt : Set

    curvatureDriftReceipt : Set
    gradBDriftReceipt : Set
    finiteOrbitWidthReceipt : Set
    noSecularRadialDriftReceipt : Set
    energeticParticleOrbitReceipt : Set

    inducedElectricFieldGlobalReceipt : Set
    actuatorSpectrumReceipt : Set
    coilCurrentRealizabilityReceipt : Set
    controlPowerReceipt : Set

    residualInvariantProfile : Invariant.TrappedParticleInvariantProfile
    candidateReference : String

open ToroidalAlfvenZeroBounceCandidate public

record ToroidalAlfvenEmbeddingAcceptance
    (population : ZeroBounce.DeclaredParticlePopulation)
    (candidate : ToroidalAlfvenZeroBounceCandidate population)
    (bestKnownReference : Invariant.TrappedParticleInvariantProfile) : Set₁ where
  constructor toroidal-alfven-embedding-acceptance
  field
    zeroMirrorSeedPreservedGlobally : Set
    noSecularRadialDrift : Set
    sameOrBetterResidualInvariant :
      Invariant.SameOrBetterTrappedParticleInvariant
        (residualInvariantProfile candidate)
        bestKnownReference
    finiteBetaEquilibriumAccepted : Set
    dynamicControlAccepted : Set
    engineeringRealizabilityAccepted : Set
    acceptanceReference : String

open ToroidalAlfvenEmbeddingAcceptance public

record ToroidalAlfvenFrontierBoundary : Set where
  constructor toroidal-alfven-frontier-boundary
  field
    zeroMirrorForceSolvesAllGuidingCentreDrift : Bool
    zeroMirrorForceSolvesAllGuidingCentreDriftIsFalse :
      zeroMirrorForceSolvesAllGuidingCentreDrift ≡ false

    curvatureIsNextPrimaryGeometricResidual : Bool
    curvatureIsNextPrimaryGeometricResidualIsTrue :
      curvatureIsNextPrimaryGeometricResidual ≡ true

    toroidalEmbeddingMustPreserveBestKnownBenchmark : Bool
    toroidalEmbeddingMustPreserveBestKnownBenchmarkIsTrue :
      toroidalEmbeddingMustPreserveBestKnownBenchmark ≡ true

canonicalToroidalAlfvenFrontierBoundary : ToroidalAlfvenFrontierBoundary
canonicalToroidalAlfvenFrontierBoundary =
  toroidal-alfven-frontier-boundary
    false refl
    true refl
    true refl
