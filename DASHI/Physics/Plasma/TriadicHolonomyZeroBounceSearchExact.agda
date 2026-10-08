module DASHI.Physics.Plasma.TriadicHolonomyZeroBounceSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.Base369BinaryTernaryRefinement as R23
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce
import DASHI.Physics.Plasma.DynamicZeroBounceAdmissibilityExact as Dynamic

------------------------------------------------------------------------
-- PURE-TRIADIC HOLONOMY / CONTROL-RESOLUTION SEARCH
--
-- Search depth n denotes C_(3^(n+1)): n=0,1,2 gives C3,C9,C27.  This is an
-- exact arithmetic resolution coordinate.  It does not assert that an actuator
-- array physically realizes every depth or that finer phase resolution improves
-- confinement monotonically.
------------------------------------------------------------------------

pureTriadicResolution : Nat → R23.Resolution23
pureTriadicResolution n = R23.resolution23 0 (suc n)

pureTriadicSectorCount : Nat → Nat
pureTriadicSectorCount n = R23.sectorCount (pureTriadicResolution n)

pureTriadicDepth0Is3 : pureTriadicSectorCount 0 ≡ 3
pureTriadicDepth0Is3 = refl

pureTriadicDepth1Is9 : pureTriadicSectorCount 1 ≡ 9
pureTriadicDepth1Is9 = refl

pureTriadicDepth2Is27 : pureTriadicSectorCount 2 ≡ 27
pureTriadicDepth2Is27 = refl

record TriadicHolonomySearchCandidate
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor triadic-holonomy-search-candidate
  field
    ternaryDepth : Nat
    spatialFrameHolonomyReceipt : Set
    temporalPhaseLawReceipt : Set
    magneticWellPlacementReceipt : Set
    radialWellDepthProfileReceipt : Set
    movingMinimumTrajectoryReceipt : Set

    dynamicAdmissibility :
      Dynamic.DynamicDetrappingAdmissibility population
    zeroBounceReceipt : ZeroBounce.ZeroBounceReceipt population

    residualBestKnownInvariantBenchmarkReceipt : Set
    finiteBetaEquilibriumReceipt : Set
    divergenceFreeFieldReceipt : Set
    coilOrActuatorRealizabilityReceipt : Set
    controlBandwidthReceipt : Set
    candidateReference : String

open TriadicHolonomySearchCandidate public

record AcceptedTriadicHolonomyCandidate
    (population : ZeroBounce.DeclaredParticlePopulation)
    (candidate : TriadicHolonomySearchCandidate population) : Set₁ where
  constructor accepted-triadic-holonomy-candidate
  field
    zeroBounceIsSatisfied : Set
    bestKnownTrappedParticleReferenceNotWorsened : Set
    dynamicHeatingAndResonanceGateSatisfied : Set
    finiteBetaEmbeddingSatisfied : Set
    engineeringRealizabilitySatisfied : Set
    acceptanceReference : String

open AcceptedTriadicHolonomyCandidate public

record TriadicHolonomySearchBoundary : Set where
  constructor triadic-holonomy-search-boundary
  field
    c3c9c27ArithmeticAnchorExact : Bool
    c3c9c27ArithmeticAnchorExactIsTrue :
      c3c9c27ArithmeticAnchorExact ≡ true

    everyPureTriadicDepthPhysicallyRealized : Bool
    everyPureTriadicDepthPhysicallyRealizedIsFalse :
      everyPureTriadicDepthPhysicallyRealized ≡ false

    finerTriadicResolutionAlwaysImprovesConfinement : Bool
    finerTriadicResolutionAlwaysImprovesConfinementIsFalse :
      finerTriadicResolutionAlwaysImprovesConfinement ≡ false

    zeroBounceGatePrecedesCommercialScoring : Bool
    zeroBounceGatePrecedesCommercialScoringIsTrue :
      zeroBounceGatePrecedesCommercialScoring ≡ true

canonicalTriadicHolonomySearchBoundary : TriadicHolonomySearchBoundary
canonicalTriadicHolonomySearchBoundary =
  triadic-holonomy-search-boundary
    true refl
    false refl
    false refl
    true refl
