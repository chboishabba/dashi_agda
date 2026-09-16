module DASHI.Reasoning.LocalFibreHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Topology.ClopenNDimFibreBoundary as NDim
import DASHI.Topology.TetrationalGateField as Gate
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Topology.WormSoilPantsSheafBoundary as WormPants
import DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact as ReductionBridge
import DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact as SectionReduction
import DASHI.Reasoning.TypedHyperfabricLocalRefinementBridgeExact as LocalRefinement
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as PantsGluing
import DASHI.Reasoning.TypedHyperfabricActionCrossingTransportExact as CrossingTransport
import DASHI.Reasoning.MaleCNSTypedHyperfabricChartProjectionExact as MaleCNSChart
import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hypercube

------------------------------------------------------------------------
-- LOCAL FIBRE HYPERFABRIC ROLE MAP
------------------------------------------------------------------------

TypedHyperfabricSurface : Set → Set → Set₁
TypedHyperfabricSurface = Hyperfabric.TypedHyperfabric

GlobalSectionSurface :
  {Vertex Edge : Set} →
  Hyperfabric.TypedHyperfabric Vertex Edge → Set₁
GlobalSectionSurface = Hyperfabric.GlobalSection

HyperfabricTraceSurface : Set → Set
HyperfabricTraceSurface = Hyperfabric.HyperfabricTrace

record LocalFibreAuthorityMap : Set where
  constructor local-fibre-authority-map
  field
    baseAndIncidenceOwner : String
    localStalkOwner : String
    restrictionTransportOwner : String
    globalCompatibilityOwner : String
    localRefinementOwner : String
    fibreDimensionOwner : String
    towerRecursionOwner : String
    pantsGluingOwner : String
    braidPathIdentityOwner : String
    symmetryQuotientOwner : String
    chartGeometryOwner : String
    interpretation : String

open LocalFibreAuthorityMap public

canonicalLocalFibreAuthorityMap : LocalFibreAuthorityMap
canonicalLocalFibreAuthorityMap = local-fibre-authority-map
  "DASHI.Reasoning.TypedHyperfabricCore.TypedHyperfabric: Vertex/Edge + incidence"
  "DASHI.Reasoning.TypedHyperfabricCore.vertexStalk / edgeStalk"
  "DASHI.Reasoning.TypedHyperfabricCore.restrict + TypedHyperfabricActionCrossingTransportExact.transportTrace"
  "DASHI.Reasoning.TypedHyperfabricCore.GlobalSection.compatible"
  "DASHI.Reasoning.TypedHyperfabricLocalRefinementBridgeExact.LocalStalkRefinement"
  "DASHI.Topology.ClopenNDimFibreBoundary.ClopenBallDescriptor / FiniteFibreAt"
  "DASHI.Topology.TetrationalGateField.TowerTransition"
  "DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact.HyperfabricPantsGluing over RelationalBranchCobordismGeometry.InterfaceMatch"
  "DASHI.Reasoning.TypedHyperfabricActionCrossingTransportExact over ActionCrossingTraceCalculusExact + BraidedEvidenceTraceBidiCrossPollination2026Exact"
  "DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact.ConsumerInvisibleSymmetry"
  "DASHI.Biology.TernaryHypercubeHyperfabricExact (carrier/transition-geometry separation)"
  "The local-fibre architecture is now a composition of existing theorem surfaces plus thin adapters only. TypedHyperfabric owns compatible GlobalSections in Set₁. Local refinement is pinned to refineWithinChart; pants gluing requires the canonical five-coordinate InterfaceMatch after domain interpretation of edge stalks; ordered action-crossing traces transport compatible sections through a domain-supplied step while preserving order/provenance and refusing automatic reversibility or braid-group promotion. Consumer reduction still acts through Set-sized selected-section codes. MaleCNS remains only one witness of the general architecture."

------------------------------------------------------------------------
-- Exact donor anchors.
------------------------------------------------------------------------

oneDimTriadicChildren : NDim.immediateChildCount 1 ≡ 3
oneDimTriadicChildren = NDim.oneDimChildren

twoDimTriadicChildren : NDim.immediateChildCount 2 ≡ 9
twoDimTriadicChildren = NDim.twoDimChildren

threeDimTriadicChildren : NDim.immediateChildCount 3 ≡ 27
threeDimTriadicChildren = NDim.threeDimChildren

refinementAndTowerAreDistinctTransitions :
  Gate.refineWithinChart ≡ Gate.openTowerLevel → ⊥
refinementAndTowerAreDistinctTransitions ()

fibreDimensionAndTowerAreDistinctTransitions :
  Gate.increaseFibreDimension ≡ Gate.openTowerLevel → ⊥
fibreDimensionAndTowerAreDistinctTransitions ()

localRefinementLivesOnTypedHyperfabricSections :
  LocalRefinement.refinementActsOnDeclaredVertexStalkValues
    LocalRefinement.canonicalTypedHyperfabricLocalRefinementBoundary ≡ true
localRefinementLivesOnTypedHyperfabricSections = refl

localRefinementDoesNotOpenTower :
  LocalRefinement.refinementImpliesOpenTowerLevel
    LocalRefinement.canonicalTypedHyperfabricLocalRefinementBoundary ≡ false
localRefinementDoesNotOpenTower = refl

localRefinementDoesNotLiftFibreDimension :
  LocalRefinement.refinementImpliesIncreaseFibreDimension
    LocalRefinement.canonicalTypedHyperfabricLocalRefinementBoundary ≡ false
localRefinementDoesNotLiftFibreDimension = refl

pantsOutputMultiplicityIsLocal : Pants.outputCount Pants.composedOneToThree ≡ 3
pantsOutputMultiplicityIsLocal = Pants.composedOutputCountIsThree

pantsPathSensitiveSplitCanConserveCapacity :
  Pants.CapacityConservative Pants.phaseChangedJunction
pantsPathSensitiveSplitCanConserveCapacity =
  Pants.phaseChangedCapacityConservative

pantsSeamRequiresCanonicalInterfaceMatch :
  PantsGluing.canonicalInterfaceMatchRequired
    PantsGluing.canonicalTypedHyperfabricPantsGluingBoundary ≡ true
pantsSeamRequiresCanonicalInterfaceMatch = refl

pantsSeamDoesNotRewriteTopologyByItself :
  PantsGluing.interfaceMatchAutomaticallyRewritesIncidence
    PantsGluing.canonicalTypedHyperfabricPantsGluingBoundary ≡ false
pantsSeamDoesNotRewriteTopologyByItself = refl

braidCrossingRetainsIdentity :
  Braid.coordinationWithoutFusion Braid.canonicalBraidedEvidenceBoundary ≡ true
braidCrossingRetainsIdentity = refl

orderedCrossingTransportPreservesCompatibilityTyping :
  CrossingTransport.crossingStepMapsCompatibleSectionToCompatibleSection
    CrossingTransport.canonicalTypedHyperfabricActionCrossingBoundary ≡ true
orderedCrossingTransportPreservesCompatibilityTyping = refl

orderedCrossingTransportDoesNotPromoteBraidGroup :
  CrossingTransport.actionTraceAutomaticallyBraidGroupElement
    CrossingTransport.canonicalTypedHyperfabricActionCrossingBoundary ≡ false
orderedCrossingTransportDoesNotPromoteBraidGroup = refl

hypercubeCarrierDoesNotFixTransitionGeometry :
  Hypercube.allowsDirectPoleJump Hypercube.mediatedPathGeometry ≡ false
hypercubeCarrierDoesNotFixTransitionGeometry =
  Hypercube.mediatedGeometryBlocksDirectPoleJump

selectedSectionCodesUseCanonicalConsumerReduction :
  SectionReduction.selectedSectionCodeMayServeAsFineReductionState
    SectionReduction.canonicalHyperfabricConsumerReductionBoundary ≡ true
selectedSectionCodesUseCanonicalConsumerReduction = refl

globalSectionUniverseRemainsExplicit :
  SectionReduction.globalSectionUniverseIsNotForcedIntoSet
    SectionReduction.canonicalHyperfabricConsumerReductionBoundary ≡ true
globalSectionUniverseRemainsExplicit = refl

maleCNSPairChartComesFromGlobalSections :
  MaleCNSChart.chartProjectionComesFromGlobalSectionEdgeValues
    MaleCNSChart.canonicalMaleCNSHyperfabricChartProjectionBoundary ≡ true
maleCNSPairChartComesFromGlobalSections = refl

maleCNSSelectedSectionCarrierIsChartCodeNotPhysicalIncidence :
  MaleCNSChart.selectedSectionCarrierIsChartCodeNotPhysicalIncidence
    MaleCNSChart.canonicalMaleCNSHyperfabricChartProjectionBoundary ≡ true
maleCNSSelectedSectionCarrierIsChartCodeNotPhysicalIncidence = refl

maleCNSRuntimeHyperfabricRoundtripIsLosslessForDeclaredConsumer :
  MaleCNSChart.empiricalHyperfabricRoundtripLosslessForDeclaredConsumer
    MaleCNSChart.canonicalMaleCNSHyperfabricChartProjectionBoundary ≡ true
maleCNSRuntimeHyperfabricRoundtripIsLosslessForDeclaredConsumer = refl

maleCNSSenderGainProjectionIsExactButNotSufficiency :
  MaleCNSChart.exactProjectionPromotesSufficiency
    MaleCNSChart.canonicalMaleCNSHyperfabricChartProjectionBoundary ≡ false
maleCNSSenderGainProjectionIsExactButNotSufficiency = refl

maleCNSCoarseCompleteSupportIsNotRawPhysicalHypergraph :
  MaleCNSChart.aggregatedRegionSupportEqualsRawPhysicalSynapseHypergraph
    MaleCNSChart.canonicalMaleCNSHyperfabricChartProjectionBoundary ≡ false
maleCNSCoarseCompleteSupportIsNotRawPhysicalHypergraph = refl

------------------------------------------------------------------------
-- The symmetry/quotient rule is already owned canonically.
------------------------------------------------------------------------

data SymmetryAloneCreatesQuotientAuthority : Set where
symmetryStillNeedsConsumerInvariance : SymmetryAloneCreatesQuotientAuthority → ⊥
symmetryStillNeedsConsumerInvariance ()

------------------------------------------------------------------------
-- Historical MaleCNS eight-feature family = one selected chart, not fibre
-- cardinality. Retained for compatibility with existing imports.
------------------------------------------------------------------------

data LegacyNDimChartCoordinate : Set where
  directForward : LegacyNDimChartCoordinate
  directReverse : LegacyNDimChartCoordinate
  twoHopForward : LegacyNDimChartCoordinate
  twoHopReverse : LegacyNDimChartCoordinate
  commonInput : LegacyNDimChartCoordinate
  commonOutput : LegacyNDimChartCoordinate
  signedForward : LegacyNDimChartCoordinate
  signedReverse : LegacyNDimChartCoordinate

data GlobalFixedFibreCount : Set where
globalFibreCountIsNotPrimitive : GlobalFixedFibreCount → ⊥
globalFibreCountIsNotPrimitive ()

data EightIsUnderlyingFibreCardinality : Set where
eightIsOnlyOneDeclaredChart : EightIsUnderlyingFibreCardinality → ⊥
eightIsOnlyOneDeclaredChart ()

record MaleCNSChartBoundary : Set where
  constructor malecns-chart-boundary
  field
    typedHyperfabricCoreRemainsCanonicalKernel : Bool
    typedHyperfabricCoreRemainsCanonicalKernelIsTrue :
      typedHyperfabricCoreRemainsCanonicalKernel ≡ true
    eightCoordinatesAreOneDeclaredChart : Bool
    eightCoordinatesAreOneDeclaredChartIsTrue :
      eightCoordinatesAreOneDeclaredChart ≡ true
    chartCoordinateCountEqualsUnderlyingFibreCount : Bool
    chartCoordinateCountEqualsUnderlyingFibreCountIsFalse :
      chartCoordinateCountEqualsUnderlyingFibreCount ≡ false
    localFibreMultiplicityMayVaryByBaseLocality : Bool
    localFibreMultiplicityMayVaryByBaseLocalityIsTrue :
      localFibreMultiplicityMayVaryByBaseLocality ≡ true
    localRefinementRequiresGlobalTimeStep : Bool
    localRefinementRequiresGlobalTimeStepIsFalse :
      localRefinementRequiresGlobalTimeStep ≡ false
    increaseFibreDimensionEqualsOpenTowerLevel : Bool
    increaseFibreDimensionEqualsOpenTowerLevelIsFalse :
      increaseFibreDimensionEqualsOpenTowerLevel ≡ false
    pantsSplitMergeMayBeNary : Bool
    pantsSplitMergeMayBeNaryIsTrue :
      pantsSplitMergeMayBeNary ≡ true
    recombinationAutomaticallyErasesPathMemory : Bool
    recombinationAutomaticallyErasesPathMemoryIsFalse :
      recombinationAutomaticallyErasesPathMemory ≡ false
    symmetryAloneCreatesQuotientAuthority : Bool
    symmetryAloneCreatesQuotientAuthorityIsFalse :
      symmetryAloneCreatesQuotientAuthority ≡ false
    consumerCompressionCollapsesPhysicalTopology : Bool
    consumerCompressionCollapsesPhysicalTopologyIsFalse :
      consumerCompressionCollapsesPhysicalTopology ≡ false
    localFibreOwnerDefinesParallelSheafKernel : Bool
    localFibreOwnerDefinesParallelSheafKernelIsFalse :
      localFibreOwnerDefinesParallelSheafKernel ≡ false

canonicalMaleCNSChartBoundary : MaleCNSChartBoundary
canonicalMaleCNSChartBoundary =
  malecns-chart-boundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Missing-fields ledger.
------------------------------------------------------------------------

record LocalFibreMissingFields : Set where
  constructor local-fibre-missing-fields
  field
    genericRefinementActsOnTypedHyperfabricStalks : Bool
    pantsInterfaceMatchLiftedToGenericHyperfabricGluing : Bool
    braidDeformationLiftedToGenericHyperfabricTransport : Bool
    selectedSectionCodeConsumerReductionBridgeConstructed : Bool
    directGlobalSectionReductionAvoided : Bool
    maleCNSPhysicalIncidenceInstanceConstructed : Bool
    maleCNSChartProjectionFromGlobalSectionsConstructed : Bool
    maleCNSSelectedSectionCarrierConstructed : Bool
    note : String

open LocalFibreMissingFields public

currentLocalFibreMissingFields : LocalFibreMissingFields
currentLocalFibreMissingFields = local-fibre-missing-fields
  true
  true
  true
  true
  true
  false
  true
  true
  "The three generic adapter seams are now source-present without a parallel ontology: TypedHyperfabricLocalRefinementBridgeExact pins local section refinement to refineWithinChart; TypedHyperfabricPantsGluingBridgeExact lifts the canonical five-coordinate InterfaceMatch to a typed seam certificate without rewriting topology; TypedHyperfabricActionCrossingTransportExact transports compatible GlobalSections along ordered crossing traces with trace order retained as provenance and no automatic reversibility/braid-group promotion. Consumer reduction remains universe-correct through Set-sized selected-section codes. MaleCNS chart realization is paid, while source-bound raw neuron/synapse physical incidence remains distinct and unpaid."
