module DASHI.Physics.Plasma.CommercialConfinementParetoHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement
import DASHI.Physics.Plasma.CommercialFusionPlantObjectiveExact as Plant
import DASHI.Physics.Plasma.GreenwaldDensityOperatingEnvelopeBidiExact as Density

------------------------------------------------------------------------
-- COMMERCIAL-CONFINEMENT PARETO HYPERFABRIC
--
-- Tokamak, spherical-tokamak and stellarator are points/subfamilies in the
-- architecture search, not terminal categories.  The repo-native N-dimensional
-- Pareto owner lets a consumer search richer field/current/topology designs
-- without scalarising plant economics into one physics number.
------------------------------------------------------------------------

data ArchitectureClass : Set where
  conventionalTokamak : ArchitectureClass
  optimizedStellarator : ArchitectureClass
  sphericalTokamak : ArchitectureClass
  highFieldHTSTokamak : ArchitectureClass
  mixedExternalTransformCurrent : ArchitectureClass
  hyperfabricOptimizedConfinement : ArchitectureClass

record CommercialConfinementCandidate : Set₁ where
  constructor commercial-confinement-candidate
  field
    architectureClass : ArchitectureClass
    plasma : Confinement.MagneticConfinementState
    plant : Plant.CommercialFusionPlantState plasma
    densityEnvelope : Density.DensityOperatingEnvelope plasma

    fieldTopologyReceipt : Set
    aspectRatioAndCompactnessReceipt : Set
    highFieldHTSReceipt : Set
    rotationalTransformReceipt : Set
    bootstrapAndDrivenCurrentReceipt : Set
    conductingWallStabilizationReceipt : Set
    plasmaWallCompatibilityReceipt : Set
    divertorAndExhaustReceipt : Set
    disruptionOrGracefulFailureReceipt : Set
    continuousControlReceipt : Set
    manufacturableCoilReceipt : Set
    maintenanceGeometryReceipt : Set

    candidateReference : String

open CommercialConfinementCandidate public

------------------------------------------------------------------------
-- Commercial axes are explicitly declared semantics for the existing Pareto
-- hyperfabric.  Lower cost along an axis means better according to the chosen
-- consumer encoding; no universal scalar score is introduced here.
------------------------------------------------------------------------

data CommercialAxis : Set where
  netElectricDeficit : CommercialAxis
  recirculatingPowerBurden : CommercialAxis
  plantCapitalBurden : CommercialAxis
  replacementAndMaintenanceBurden : CommercialAxis
  unplannedShutdownBurden : CommercialAxis
  fuelCycleBurden : CommercialAxis
  plasmaFacingComponentBurden : CommercialAxis
  magnetAndCryogenicBurden : CommercialAxis
  currentDriveBurden : CommercialAxis
  exhaustBurden : CommercialAxis
  geometricComplexityBurden : CommercialAxis
  empiricalUncertaintyBurden : CommercialAxis

commercialAxisReference : CommercialAxis → String
commercialAxisReference netElectricDeficit = "maximize sustained net electric export"
commercialAxisReference recirculatingPowerBurden = "minimize plant recirculating electrical power"
commercialAxisReference plantCapitalBurden = "minimize buildable plant capital burden"
commercialAxisReference replacementAndMaintenanceBurden = "maximize maintainability and component lifetime"
commercialAxisReference unplannedShutdownBurden = "minimize disruption/unplanned outage burden"
commercialAxisReference fuelCycleBurden = "close fuel cycle with low inventory and processing burden"
commercialAxisReference plasmaFacingComponentBurden = "minimize first-wall/divertor damage and replacement burden"
commercialAxisReference magnetAndCryogenicBurden = "minimize magnet/cryogenic burden at required field"
commercialAxisReference currentDriveBurden = "minimize steady-state current-drive power burden"
commercialAxisReference exhaustBurden = "minimize heat/particle exhaust burden"
commercialAxisReference geometricComplexityBurden = "minimize manufacturing/alignment/maintenance complexity"
commercialAxisReference empiricalUncertaintyBurden = "minimize unsupported cross-device extrapolation"

record CommercialParetoInstantiation
    (problem : Pareto.ConsumerMDLProblem)
    (costs : Pareto.CostHyperfabric problem) : Set₁ where
  constructor commercial-pareto-instantiation
  field
    decodeCandidate : Pareto.Model problem → CommercialConfinementCandidate
    axisEmbedding : CommercialAxis → Pareto.Axis costs
    axisEmbeddingReference :
      (axis : CommercialAxis) →
      Pareto.axisReference costs (axisEmbedding axis) ≡ commercialAxisReference axis
    nDimensionalView : NDim.NDimParetoView costs
    commercialConsumerReference : String

open CommercialParetoInstantiation public

CommercialWeaklyDominates :
  ∀ {problem : Pareto.ConsumerMDLProblem}
    {costs : Pareto.CostHyperfabric problem} →
  CommercialParetoInstantiation problem costs →
  Pareto.Model problem → Pareto.Model problem → Set
CommercialWeaklyDominates {costs = costs} inst left right =
  (axis : CommercialAxis) →
  Pareto.cost costs (axisEmbedding inst axis) left ≤
  Pareto.cost costs (axisEmbedding inst axis) right

fullRepoParetoDominanceImpliesCommercialDominance :
  ∀ {problem : Pareto.ConsumerMDLProblem}
    {costs : Pareto.CostHyperfabric problem}
    (inst : CommercialParetoInstantiation problem costs)
    {left right : Pareto.Model problem} →
  Pareto.WeaklyDominates costs left right →
  CommercialWeaklyDominates inst left right
fullRepoParetoDominanceImpliesCommercialDominance inst dominates axis =
  dominates (axisEmbedding inst axis)

------------------------------------------------------------------------
-- "Better than stellarator" means an inhabited dominance/eligibility receipt,
-- never merely belonging to a newer architecture class.
------------------------------------------------------------------------

record BetterThanReferenceArchitecture
    {problem : Pareto.ConsumerMDLProblem}
    {costs : Pareto.CostHyperfabric problem}
    (inst : CommercialParetoInstantiation problem costs)
    (candidate reference : Pareto.Model problem) : Set₁ where
  constructor better-than-reference-architecture
  field
    candidateEligible : Pareto.Eligible problem candidate
    referenceEligible : Pareto.Eligible problem reference
    commercialDominance : CommercialWeaklyDominates inst candidate reference
    atLeastOneStrictCommercialImprovementReceipt : Set
    sameCommercialConsumerReceipt : Set
    sameEvidenceStandardReceipt : Set
    comparisonReference : String

open BetterThanReferenceArchitecture public

record CommercialConfinementParetoBoundary : Set where
  constructor commercial-confinement-pareto-boundary
  field
    stellaratorIsTerminalSearchCategory : Bool
    stellaratorIsTerminalSearchCategoryIsFalse :
      stellaratorIsTerminalSearchCategory ≡ false

    newArchitectureLabelProvesCommercialSuperiority : Bool
    newArchitectureLabelProvesCommercialSuperiorityIsFalse :
      newArchitectureLabelProvesCommercialSuperiority ≡ false

    scalarFusionGainAloneOrdersCommercialArchitectures : Bool
    scalarFusionGainAloneOrdersCommercialArchitecturesIsFalse :
      scalarFusionGainAloneOrdersCommercialArchitectures ≡ false

    existingNDimParetoOwnerIsReused : Bool
    existingNDimParetoOwnerIsReusedIsTrue :
      existingNDimParetoOwnerIsReused ≡ true

    hyperfabricMaySearchMixedTopologyCurrentAndWallDesigns : Bool
    hyperfabricMaySearchMixedTopologyCurrentAndWallDesignsIsTrue :
      hyperfabricMaySearchMixedTopologyCurrentAndWallDesigns ≡ true

canonicalCommercialConfinementParetoBoundary :
  CommercialConfinementParetoBoundary
canonicalCommercialConfinementParetoBoundary =
  commercial-confinement-pareto-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
