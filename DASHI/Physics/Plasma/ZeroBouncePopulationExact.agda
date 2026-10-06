module DASHI.Physics.Plasma.ZeroBouncePopulationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ZERO-BOUNCE POPULATION TARGET
--
-- The primary target is stronger than omnigenity: declared particles should
-- remain passing, with no magnetic-mirror turning point / parallel-velocity
-- reversal.  Because static toroidal magnetic fields cannot eliminate trapped
-- particles altogether, every claim is population- and regime-indexed.
------------------------------------------------------------------------

record DeclaredParticlePopulation : Set₁ where
  constructor declared-particle-population
  field
    Species : Set
    EnergyClass : Set
    PitchClass : Set
    RadialClass : Set
    populationReference : String

open DeclaredParticlePopulation public

record ZeroBounceReceipt (population : DeclaredParticlePopulation) : Set₁ where
  constructor zero-bounce-receipt
  field
    noMagneticMirrorTurningPointReceipt : Set
    noParallelVelocityReversalReceipt : Set
    continuouslyPassingOrbitReceipt : Set
    sameEnergyPitchPopulationReceipt : Set
    sameRadialDomainReceipt : Set
    guidingCentreValidityReceipt : Set
    zeroBounceReference : String

open ZeroBounceReceipt public

record ResidualBounceReceipt (population : DeclaredParticlePopulation) : Set₁ where
  constructor residual-bounce-receipt
  field
    trappedSubsetReceipt : Set
    trappedFractionReceipt : Set
    bounceActionReceipt : Set
    maximumJReceipt : Set
    bounceAveragedRadialDriftReceipt : Set
    residualReference : String

open ResidualBounceReceipt public

record ZeroBounceBoundary : Set where
  constructor zero-bounce-boundary
  field
    zeroBounceStrongerThanZeroBounceAveragedRadialDrift : Bool
    zeroBounceStrongerThanZeroBounceAveragedRadialDriftIsTrue :
      zeroBounceStrongerThanZeroBounceAveragedRadialDrift ≡ true

    universalStaticToroidalZeroBouncePromoted : Bool
    universalStaticToroidalZeroBouncePromotedIsFalse :
      universalStaticToroidalZeroBouncePromoted ≡ false

    shallowMagneticWellsAloneProveZeroBounce : Bool
    shallowMagneticWellsAloneProveZeroBounceIsFalse :
      shallowMagneticWellsAloneProveZeroBounce ≡ false

    residualBounceStillRequiresBestKnownInvariantBenchmark : Bool
    residualBounceStillRequiresBestKnownInvariantBenchmarkIsTrue :
      residualBounceStillRequiresBestKnownInvariantBenchmark ≡ true

canonicalZeroBounceBoundary : ZeroBounceBoundary
canonicalZeroBounceBoundary =
  zero-bounce-boundary
    true refl
    false refl
    false refl
    true refl

staticToroidalTrappingSource : String
staticToroidalTrappingSource =
  "Dudt et al., Journal of Plasma Physics 90 (2024), Magnetic fields with general omnigenity: trapped particles cannot be avoided altogether in toroidal geometry."
