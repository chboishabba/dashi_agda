module DASHI.Physics.Plasma.ToroidalConstantMagnitudeABCMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.ToroidalConstantMagnitudeAlfvenicFlowExact as A
import DASHI.Physics.Plasma.ToroidalConstantMagnitudeCGLAnisotropyExact as B
import DASHI.Physics.Plasma.ToroidalConstantMagnitudeGeodesic3DEquilibriumExact as C
import DASHI.Physics.Plasma.TriadicPhaseConjugationControlExact as Phase
import DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact as Invariant
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- ABC MAX-CUT FOR CONSTANT-|B| TOROIDAL ZERO-BOUNCE GEOMETRY
--
-- Route A: exact ideal-MHD Alfvenic flow continuation.
-- Route B: exact CGL anisotropic continuation, but firehose-marginal in the
--          constant-pressure seed.
-- Route C: static scalar-pressure 3-D continuation requiring geodesic magnetic
--          field lines on flux surfaces.
--
-- All routes preserve the same zero-bounce object and must still pay orbit,
-- stability, engineering and best-known-reference comparison obligations.
------------------------------------------------------------------------

data ForceBalanceRoute : Set where
  alfvenicFlowRoute : ForceBalanceRoute
  cglAnisotropyRoute : ForceBalanceRoute
  geodesic3DRoute : ForceBalanceRoute

record ToroidalConstantMagnitudeABCMaxCut
    (population : ZeroBounce.DeclaredParticlePopulation)
    (seed : Seed.ToroidalConstantMagnitudeSeed population) : Set₁ where
  constructor toroidal-constant-magnitude-abc-max-cut
  field
    triadicConjugationControl : Phase.TriadicConjugationControlReceipt

    routeA : A.AlfvenicFlowBalanceReceipt population seed
    routeB : B.CGLAnisotropicBalanceReceipt population seed
    routeC : C.GeodesicFluxSurfaceBalanceReceipt population

    sameZeroBounceObjectAcrossRoutesReceipt : Set
    sameMagneticMagnitudeObservableReceipt : Set
    sameCurvatureObservableReceipt : Set
    sameSpeciesEnergyPitchPopulationReceipt : Set

    routeAStabilityAndPowerReceipt : Set
    routeBStrictStabilityMarginOrHybridizationReceipt : Set
    routeCEmbeddingAndCoilRealizabilityReceipt : Set

    finiteOrbitWidthReceipt : Set
    energeticParticleReceipt : Set
    collisionTurbulenceReceipt : Set
    reference : String

open ToroidalConstantMagnitudeABCMaxCut public

record AcceptedABCContinuation
    {population : ZeroBounce.DeclaredParticlePopulation}
    {seed : Seed.ToroidalConstantMagnitudeSeed population}
    (cut : ToroidalConstantMagnitudeABCMaxCut population seed)
    (referenceProfile : Invariant.TrappedParticleInvariantProfile) : Set₁ where
  constructor accepted-abc-continuation
  field
    selectedRoute : ForceBalanceRoute
    selectedRouteForceBalanceAccepted : Set
    zeroBouncePreserved : Set
    finiteOrbitWidthAccepted : Set
    energeticParticleAccepted : Set
    stabilityAccepted : Set
    engineeringAccepted : Set
    sameOrBetterBestKnownReferenceReceipt : Set
    sameEvidenceStandardReceipt : Set
    acceptanceReference : String

open AcceptedABCContinuation public

record ABCMaxCutBoundary : Set where
  constructor abc-max-cut-boundary
  field
    routeAIdentityAloneProvesStableReactor : Bool
    routeAIdentityAloneProvesStableReactorIsFalse :
      routeAIdentityAloneProvesStableReactor ≡ false

    routeBFirehoseMarginalSeedAcceptedAsOperatingPoint : Bool
    routeBFirehoseMarginalSeedAcceptedAsOperatingPointIsFalse :
      routeBFirehoseMarginalSeedAcceptedAsOperatingPoint ≡ false

    routeCMaySkipGeodesicCondition : Bool
    routeCMaySkipGeodesicConditionIsFalse :
      routeCMaySkipGeodesicCondition ≡ false

    e8OrZetaStructurePromotedAsPlasmaPhysics : Bool
    e8OrZetaStructurePromotedAsPlasmaPhysicsIsFalse :
      e8OrZetaStructurePromotedAsPlasmaPhysics ≡ false

    bestKnownReferenceComparisonRemainsMandatory : Bool
    bestKnownReferenceComparisonRemainsMandatoryIsTrue :
      bestKnownReferenceComparisonRemainsMandatory ≡ true

canonicalABCMaxCutBoundary : ABCMaxCutBoundary
canonicalABCMaxCutBoundary =
  abc-max-cut-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
