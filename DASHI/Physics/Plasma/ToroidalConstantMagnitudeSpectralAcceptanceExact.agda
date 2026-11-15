module DASHI.Physics.Plasma.ToroidalConstantMagnitudeSpectralAcceptanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce
import DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.ToroidalConstantMagnitudeEquilibriumBoundaryExact as Equilibrium
import DASHI.Physics.Plasma.TriadicPhaseFourierProjectorExact as Projector
import DASHI.Physics.Plasma.FiniteAspectRatioTriadicCurvatureResidualExact as Residual
import DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact as Invariant

------------------------------------------------------------------------
-- CONSTANT-|B| TOROIDAL SPECTRAL ACCEPTANCE
--
-- This is the strongest current constructive lane:
--   constant |B|  -> literal zero magnetic-mirror force
--   div B = 0     -> global magnetic-field admissibility on the circular surface
--   C_(3^n) phase projector -> suppress declared curvature-drift harmonics
--
-- Static finite-beta scalar-pressure closure is NOT assumed; the candidate must
-- pay one of the explicit equilibrium continuation routes before promotion.
------------------------------------------------------------------------

record ToroidalConstantMagnitudeSpectralCandidate
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor toroidal-constant-magnitude-spectral-candidate
  field
    seed : Seed.ToroidalConstantMagnitudeSeed population
    equilibriumContinuation :
      Equilibrium.ConstantMagnitudeEquilibriumContinuation population seed
    phaseProjector : Projector.CyclicFourierProjectorReceipt
    finiteAspectResidual : Residual.FiniteAspectRatioCurvatureResidualReceipt

    sameCurvatureObservableAcrossProjectorReceipt : Set
    orbitalMeanRadialCurvatureClosureReceipt : Set
    projectedPointwiseResidualWithinBudgetReceipt : Set
    gradBResidualWithinBudgetReceipt : Set
    finiteOrbitWidthWithinBudgetReceipt : Set
    energeticParticleWithinBudgetReceipt : Set
    actuatorOr3DGeometryRealizabilityReceipt : Set

    residualInvariantProfile : Invariant.TrappedParticleInvariantProfile
    candidateReference : String

open ToroidalConstantMagnitudeSpectralCandidate public

record AcceptedToroidalConstantMagnitudeSpectralCandidate
    {population : ZeroBounce.DeclaredParticlePopulation}
    (candidate : ToroidalConstantMagnitudeSpectralCandidate population)
    (bestKnownReference : Invariant.TrappedParticleInvariantProfile) : Set₁ where
  constructor accepted-toroidal-constant-magnitude-spectral-candidate
  field
    exactZeroBounceAccepted : Set
    divergenceFreeAccepted : Set
    spectralCurvatureSuppressionAccepted : Set
    finiteAspectResidualAccepted : Set
    equilibriumContinuationAccepted : Set
    finiteOrbitWidthAccepted : Set
    energeticParticleAccepted : Set

    sameOrBetterReferenceInvariant :
      Invariant.SameOrBetterTrappedParticleInvariant
        (residualInvariantProfile candidate)
        bestKnownReference

    sameSpeciesEnergyPitchReceipt : Set
    sameRadialDomainReceipt : Set
    sameEquilibriumRegimeReceipt : Set
    acceptanceReference : String

open AcceptedToroidalConstantMagnitudeSpectralCandidate public

record ToroidalConstantMagnitudeSpectralBoundary : Set where
  constructor toroidal-constant-magnitude-spectral-boundary
  field
    zeroBounceMayBeRelaxedBecauseProjectorIsStrong : Bool
    zeroBounceMayBeRelaxedBecauseProjectorIsStrongIsFalse :
      zeroBounceMayBeRelaxedBecauseProjectorIsStrong ≡ false

    orbitAveragedCurvatureClosureMeansPointwiseCurvatureZero : Bool
    orbitAveragedCurvatureClosureMeansPointwiseCurvatureZeroIsFalse :
      orbitAveragedCurvatureClosureMeansPointwiseCurvatureZero ≡ false

    phaseProjectionReplacesEquilibriumClosure : Bool
    phaseProjectionReplacesEquilibriumClosureIsFalse :
      phaseProjectionReplacesEquilibriumClosure ≡ false

    bestKnownReferenceComparisonStillMandatory : Bool
    bestKnownReferenceComparisonStillMandatoryIsTrue :
      bestKnownReferenceComparisonStillMandatory ≡ true

canonicalToroidalConstantMagnitudeSpectralBoundary :
  ToroidalConstantMagnitudeSpectralBoundary
canonicalToroidalConstantMagnitudeSpectralBoundary =
  toroidal-constant-magnitude-spectral-boundary
    false refl
    false refl
    false refl
    true refl

localReplayReference : String
localReplayReference =
  "scripts/test_toroidal_constantB_clebsch_probe.py"
