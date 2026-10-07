module DASHI.Physics.Plasma.ToroidalZeroBounceGeometryParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Physics.Plasma.ToroidalZeroBounceAdmissibleConeSearchExact as Cone
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- PARETO SEARCH ONLY AFTER ADMISSIBILITY / SPECTRAL QUOTIENTING.
------------------------------------------------------------------------

data GeometryAxis : Set where
  magneticMagnitudeDefect : GeometryAxis
  geodesicCurvatureDefect : GeometryAxis
  finiteOrbitWidthDefect : GeometryAxis
  energeticParticleLossDefect : GeometryAxis
  stabilityMarginDeficit : GeometryAxis
  controlPowerBurden : GeometryAxis
  coilComplexityBurden : GeometryAxis
  bestKnownReferenceGap : GeometryAxis

geometryAxisReference : GeometryAxis → String
geometryAxisReference magneticMagnitudeDefect = "minimize variation of |B| on the declared orbit/surface chart"
geometryAxisReference geodesicCurvatureDefect = "minimize surface-tangential field-line curvature"
geometryAxisReference finiteOrbitWidthDefect = "minimize finite-orbit-width radial loss defect"
geometryAxisReference energeticParticleLossDefect = "minimize energetic-particle orbit-loss defect"
geometryAxisReference stabilityMarginDeficit = "maximize distance from declared MHD/kinetic stability boundaries"
geometryAxisReference controlPowerBurden = "minimize required active-control power"
geometryAxisReference coilComplexityBurden = "minimize coil/current geometric complexity"
geometryAxisReference bestKnownReferenceGap = "match or beat best-known optimized-stellarator consumer observables"

record AdmissibleGeometryParetoInstantiation
    {population : ZeroBounce.DeclaredParticlePopulation}
    (search : Cone.ToroidalAdmissibleConeSearch population)
    (problem : Pareto.ConsumerMDLProblem)
    (costs : Pareto.CostHyperfabric problem) : Set₁ where
  constructor admissible-geometry-pareto-instantiation
  field
    decodeModelToSearchState : Pareto.Model problem → Cone.State search
    eligibleImpliesAdmissibleConeStateReceipt : Set
    axisEmbedding : GeometryAxis → Pareto.Axis costs
    axisEmbeddingReference :
      (axis : GeometryAxis) →
      Pareto.axisReference costs (axisEmbedding axis) ≡ geometryAxisReference axis
    nDimensionalView : NDim.NDimParetoView costs
    sameConsumerReference : String

open AdmissibleGeometryParetoInstantiation public

record AcceptedGeometryParetoPoint
    {population : ZeroBounce.DeclaredParticlePopulation}
    {search : Cone.ToroidalAdmissibleConeSearch population}
    {problem : Pareto.ConsumerMDLProblem}
    {costs : Pareto.CostHyperfabric problem}
    (inst : AdmissibleGeometryParetoInstantiation search problem costs)
    (model : Pareto.Model problem) : Set₁ where
  constructor accepted-geometry-pareto-point
  field
    eligible : Pareto.Eligible problem model
    zeroBounceNotTradedAwayReceipt : Set
    sameReferencePopulationReceipt : Set
    noOtherEligibleModelStrictlyDominatesReceipt : Set
    acceptanceReference : String

open AcceptedGeometryParetoPoint public

record GeometryParetoBoundary : Set where
  constructor geometry-pareto-boundary
  field
    paretoSearchMayRescueInadmissiblePhysics : Bool
    paretoSearchMayRescueInadmissiblePhysicsIsFalse :
      paretoSearchMayRescueInadmissiblePhysics ≡ false

    scalarObjectiveDefinesFinalArchitecture : Bool
    scalarObjectiveDefinesFinalArchitectureIsFalse :
      scalarObjectiveDefinesFinalArchitecture ≡ false

    existingNDimParetoMachineryIsReused : Bool
    existingNDimParetoMachineryIsReusedIsTrue :
      existingNDimParetoMachineryIsReused ≡ true

canonicalGeometryParetoBoundary : GeometryParetoBoundary
canonicalGeometryParetoBoundary =
  geometry-pareto-boundary false refl false refl true refl
