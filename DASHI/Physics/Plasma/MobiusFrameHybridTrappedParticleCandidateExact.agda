module DASHI.Physics.Plasma.MobiusFrameHybridTrappedParticleCandidateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ProgrammableTokamakStellaratorHybridExact as Hybrid
import DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact as Invariant

------------------------------------------------------------------------
-- MOBIUS-FRAME HYBRID TRAPPED-PARTICLE CANDIDATE
--
-- This owner turns the geometry idea into a reference-comparison obligation.
-- A candidate is not promoted because it is Mobius-like; it must match or beat
-- a declared optimized-stellarator reference on the trapped-particle invariant
-- chart while separately retaining equilibrium / engineering obligations.
------------------------------------------------------------------------

record MobiusFrameHybridCandidate : Set₁ where
  constructor mobius-frame-hybrid-candidate
  field
    hybrid : Hybrid.ProgrammableHybridState
    invariantProfile : Invariant.TrappedParticleInvariantProfile

    orientableNestedFluxSurfaceReceipt : Set
    frameHolonomyReceipt : Set
    pairedOrCyclicBounceCancellationReceipt : Set
    finiteBetaEmbeddingReceipt : Set
    divergenceFreeMagneticFieldReceipt : Set
    coilRealizabilityReceipt : Set
    controlRealizabilityReceipt : Set
    candidateReference : String

open MobiusFrameHybridCandidate public

record BeatsOptimizedStellaratorTrappedParticleReference
    (candidate : MobiusFrameHybridCandidate)
    (stellaratorReference : Invariant.TrappedParticleInvariantProfile) : Set₁ where
  constructor beats-optimized-stellarator-trapped-particle-reference
  field
    sameOrBetterInvariant :
      Invariant.SameOrBetterTrappedParticleInvariant
        (invariantProfile candidate)
        stellaratorReference
    referenceIsOptimizedStellaratorReceipt : Set
    sameSpeciesEnergyPitchPopulationReceipt : Set
    sameFluxSurfaceRangeReceipt : Set
    sameOrbitModelReceipt : Set
    comparisonReference : String

open BeatsOptimizedStellaratorTrappedParticleReference public

record MobiusFrameHybridCandidateBoundary : Set where
  constructor mobius-frame-hybrid-candidate-boundary
  field
    mobiusLikeShapeAloneBeatsStellarator : Bool
    mobiusLikeShapeAloneBeatsStellaratorIsFalse :
      mobiusLikeShapeAloneBeatsStellarator ≡ false

    toyBounceActionResultIsEquilibriumProof : Bool
    toyBounceActionResultIsEquilibriumProofIsFalse :
      toyBounceActionResultIsEquilibriumProof ≡ false

    referenceDominanceIsRequiredForSameOrBetterClaim : Bool
    referenceDominanceIsRequiredForSameOrBetterClaimIsTrue :
      referenceDominanceIsRequiredForSameOrBetterClaim ≡ true

canonicalMobiusFrameHybridCandidateBoundary : MobiusFrameHybridCandidateBoundary
canonicalMobiusFrameHybridCandidateBoundary =
  mobius-frame-hybrid-candidate-boundary
    false refl
    false refl
    true refl
