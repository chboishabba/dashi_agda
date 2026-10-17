module DASHI.Physics.Plasma.ToroidalZeroBounceTriadicCurvatureSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce
import DASHI.Physics.Plasma.TriadicHolonomyZeroBounceSearchExact as TriadicSearch
import DASHI.Physics.Plasma.TriadicCurvatureDriftCancellationExact as Curvature
import DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact as Invariant

------------------------------------------------------------------------
-- TOROIDAL ZERO-BOUNCE / TRIADIC-CURVATURE SEARCH FRONTIER
--
-- A promoted candidate must keep the no-mirror target while paying the new
-- toroidal defect: curvature / finite-orbit-width radial transport.  A naive
-- toroidal helix is explicitly not accepted merely because it has high winding.
------------------------------------------------------------------------

record ToroidalZeroBounceCurvatureCandidate
    (population : ZeroBounce.DeclaredParticlePopulation)
    (space : Curvature.DriftVectorSpace) : Set₁ where
  constructor toroidal-zero-bounce-curvature-candidate
  field
    zeroBounceSearch : TriadicSearch.TriadicHolonomySearchCandidate population
    curvatureCancellation : Curvature.RecursiveTriadicCurvatureCancellation space

    constantOrControlledMagneticMagnitudeReceipt : Set
    nestedToroidalFluxSurfaceReceipt : Set
    divergenceFreeToroidalFieldReceipt : Set
    finiteBetaForceBalanceReceipt : Set

    pointwiseOrCyclicRadialCurvatureClosureReceipt : Set
    gradBDriftReceipt : Set
    finiteOrbitWidthReceipt : Set
    energeticParticleOrbitReceipt : Set
    collisionAndTurbulenceRobustnessReceipt : Set

    candidateReference : String

open ToroidalZeroBounceCurvatureCandidate public

record BeatsBestKnownToroidalTrappedParticleReference
    {population : ZeroBounce.DeclaredParticlePopulation}
    {space : Curvature.DriftVectorSpace}
    (candidate : ToroidalZeroBounceCurvatureCandidate population space)
    (reference : Invariant.TrappedParticleInvariantProfile) : Set₁ where
  constructor beats-best-known-toroidal-trapped-particle-reference
  field
    residualInvariantNoWorseReceipt : Set
    zeroBouncePrimaryTargetReceipt : Set
    radialCurvatureTransportNoWorseReceipt : Set
    finiteOrbitWidthNoWorseReceipt : Set
    sameSpeciesEnergyPitchReceipt : Set
    sameRadialDomainReceipt : Set
    sameFiniteBetaRegimeReceipt : Set
    sameOrbitIntegratorReceipt : Set
    comparisonReference : String

open BeatsBestKnownToroidalTrappedParticleReference public

record ToroidalZeroBounceCurvatureBoundary : Set where
  constructor toroidal-zero-bounce-curvature-boundary
  field
    constantBAloneEliminatesCurvatureDrift : Bool
    constantBAloneEliminatesCurvatureDriftIsFalse :
      constantBAloneEliminatesCurvatureDrift ≡ false

    naiveHelixWindingAloneAccepted : Bool
    naiveHelixWindingAloneAcceptedIsFalse :
      naiveHelixWindingAloneAccepted ≡ false

    zeroBounceCandidateMaySkipFiniteOrbitWidth : Bool
    zeroBounceCandidateMaySkipFiniteOrbitWidthIsFalse :
      zeroBounceCandidateMaySkipFiniteOrbitWidth ≡ false

    bestKnownReferenceStillRequired : Bool
    bestKnownReferenceStillRequiredIsTrue :
      bestKnownReferenceStillRequired ≡ true

canonicalToroidalZeroBounceCurvatureBoundary : ToroidalZeroBounceCurvatureBoundary
canonicalToroidalZeroBounceCurvatureBoundary =
  toroidal-zero-bounce-curvature-boundary
    false refl
    false refl
    false refl
    true refl

localPythonProbeReference : String
localPythonProbeReference =
  "scripts/cyclic_curvature_probe.py / scripts/test_cyclic_curvature_probe.py"
