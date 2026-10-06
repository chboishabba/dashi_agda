module DASHI.Physics.Plasma.ZeroBounceHybridBenchmarkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MobiusFrameHybridTrappedParticleCandidateExact as Hybrid
import DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact as Invariant
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce
import DASHI.Physics.Plasma.TriadicZeroBounceControlExact as Triadic

------------------------------------------------------------------------
-- ZERO-BOUNCE + BEST-KNOWN-INVARIANT BENCHMARK
--
-- Primary objective: no magnetic-mirror bounce for the declared reactor
-- population.  Secondary/fallback objective for any unavoidable residual set:
-- match or beat the best declared optimized-stellarator trapped-particle chart.
------------------------------------------------------------------------

record ZeroBounceHybridCandidate : Set₁ where
  constructor zero-bounce-hybrid-candidate
  field
    geometryCandidate : Hybrid.MobiusFrameHybridCandidate
    population : ZeroBounce.DeclaredParticlePopulation
    zeroBounce : ZeroBounce.ZeroBounceReceipt population
    triadicControl : Triadic.TriadicDetrappingSchedule population
    noBounceAcrossFiniteBetaEquilibriumReceipt : Set
    noBounceAcrossCollisionalBroadeningReceipt : Set
    noBounceAcrossEnergeticParticlePopulationReceipt : Set
    candidateReference : String

open ZeroBounceHybridCandidate public

record ZeroBounceAndInvariantDominance
    (candidate : ZeroBounceHybridCandidate)
    (bestKnownReference : Invariant.TrappedParticleInvariantProfile) : Set₁ where
  constructor zero-bounce-and-invariant-dominance
  field
    sameOrBetterResidualInvariant :
      Invariant.SameOrBetterTrappedParticleInvariant
        (Hybrid.invariantProfile (geometryCandidate candidate))
        bestKnownReference
    bestKnownReferenceReceipt : Set
    zeroBounceIsPrimaryObjectiveReceipt : Set
    sameSpeciesEnergyPitchPopulationReceipt : Set
    sameFiniteBetaRegimeReceipt : Set
    sameOrbitModelReceipt : Set
    dominanceReference : String

open ZeroBounceAndInvariantDominance public

record ZeroBounceHybridBoundary : Set where
  constructor zero-bounce-hybrid-boundary
  field
    zeroBounceCanBeReplacedByBounceAverageCancellation : Bool
    zeroBounceCanBeReplacedByBounceAverageCancellationIsFalse :
      zeroBounceCanBeReplacedByBounceAverageCancellation ≡ false

    triadicControlLabelAloneProvesZeroBounce : Bool
    triadicControlLabelAloneProvesZeroBounceIsFalse :
      triadicControlLabelAloneProvesZeroBounce ≡ false

    zeroBounceAloneProvesBetterReactor : Bool
    zeroBounceAloneProvesBetterReactorIsFalse :
      zeroBounceAloneProvesBetterReactor ≡ false

    bestKnownInvariantBenchmarkStillRequired : Bool
    bestKnownInvariantBenchmarkStillRequiredIsTrue :
      bestKnownInvariantBenchmarkStillRequired ≡ true

canonicalZeroBounceHybridBoundary : ZeroBounceHybridBoundary
canonicalZeroBounceHybridBoundary =
  zero-bounce-hybrid-boundary
    false refl
    false refl
    false refl
    true refl
