module DASHI.Physics.Plasma.ToroidalZeroBounceCurvatureMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce
import DASHI.Physics.Plasma.ToroidalZeroBounceTriadicCurvatureSearchExact as Search
import DASHI.Physics.Plasma.TriadicCurvatureDriftCancellationExact as Curvature
import DASHI.Physics.Plasma.TriadicPhaseFourierProjectorExact as Projector
import DASHI.Physics.Plasma.FiniteAspectRatioTriadicCurvatureResidualExact as Residual
import DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact as Invariant

------------------------------------------------------------------------
-- TOROIDAL ZERO-BOUNCE CURVATURE MAX-CUT
--
-- This is the acceptance weld for the present geometry programme.  A candidate
-- must carry literal zero-bounce intent, explicit toroidal curvature closure,
-- the C_(3^n) phase-projector mechanism, finite-aspect-ratio residual evidence,
-- and a no-worse comparison against the declared best-known trapped-particle
-- reference.  Numerical probes cannot discharge equilibrium or orbit theorems.
------------------------------------------------------------------------

record ToroidalZeroBounceCurvatureMaxCut
    (population : ZeroBounce.DeclaredParticlePopulation)
    (space : Curvature.DriftVectorSpace) : Set₁ where
  constructor toroidal-zero-bounce-curvature-max-cut
  field
    candidate : Search.ToroidalZeroBounceCurvatureCandidate population space
    phaseProjector : Projector.CyclicFourierProjectorReceipt
    finiteAspectResidual : Residual.FiniteAspectRatioCurvatureResidualReceipt

    zeroMirrorBouncePreservedReceipt : Set
    guidingCentreCurvatureObservableReceipt : Set
    phaseProjectorActsOnSameObservableReceipt : Set
    finiteAspectResidualWithinBudgetReceipt : Set

    divergenceFreeFieldReceipt : Set
    finiteBetaForceBalanceReceipt : Set
    finiteOrbitWidthWithinBudgetReceipt : Set
    energeticParticleWithinBudgetReceipt : Set
    collisionTurbulenceRobustnessWithinBudgetReceipt : Set

    maxCutReference : String

open ToroidalZeroBounceCurvatureMaxCut public

record AcceptedToroidalZeroBounceCurvatureMaxCut
    {population : ZeroBounce.DeclaredParticlePopulation}
    {space : Curvature.DriftVectorSpace}
    (cut : ToroidalZeroBounceCurvatureMaxCut population space)
    (reference : Invariant.TrappedParticleInvariantProfile) : Set₁ where
  constructor accepted-toroidal-zero-bounce-curvature-max-cut
  field
    zeroBounceAccepted : Set
    projectorMechanismAccepted : Set
    curvatureResidualAccepted : Set
    finiteOrbitWidthAccepted : Set
    equilibriumAccepted : Set
    engineeringControlAccepted : Set

    beatsReference :
      Search.BeatsBestKnownToroidalTrappedParticleReference
        (candidate cut)
        reference

    sameEvidenceStandardReceipt : Set
    acceptanceReference : String

open AcceptedToroidalZeroBounceCurvatureMaxCut public

record ToroidalZeroBounceCurvatureMaxCutBoundary : Set where
  constructor toroidal-zero-bounce-curvature-max-cut-boundary
  field
    numericalC27FloorCountsAsExactPhysicalZero : Bool
    numericalC27FloorCountsAsExactPhysicalZeroIsFalse :
      numericalC27FloorCountsAsExactPhysicalZero ≡ false

    projectorReceiptReplacesFiniteOrbitWidth : Bool
    projectorReceiptReplacesFiniteOrbitWidthIsFalse :
      projectorReceiptReplacesFiniteOrbitWidth ≡ false

    zeroBounceMayBeTradedForLowerCurvatureCost : Bool
    zeroBounceMayBeTradedForLowerCurvatureCostIsFalse :
      zeroBounceMayBeTradedForLowerCurvatureCost ≡ false

    bestKnownReferenceComparisonStillMandatory : Bool
    bestKnownReferenceComparisonStillMandatoryIsTrue :
      bestKnownReferenceComparisonStillMandatory ≡ true

canonicalToroidalZeroBounceCurvatureMaxCutBoundary :
  ToroidalZeroBounceCurvatureMaxCutBoundary
canonicalToroidalZeroBounceCurvatureMaxCutBoundary =
  toroidal-zero-bounce-curvature-max-cut-boundary
    false refl
    false refl
    false refl
    true refl
