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
import DASHI.Reasoning.MaleCNSTypedHyperfabricChartProjectionExact as MaleCNSChart
import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hypercube

------------------------------------------------------------------------
-- LOCAL FIBRE HYPERFABRIC ROLE MAP
--
-- This module is deliberately NOT a second sheaf/hyperfabric kernel.
-- TypedHyperfabricCore already owns local stalks, typed incidence, restriction,
-- global-section compatibility, obstructions, traces and provenance-preserving
-- reorganisation. The remaining repo-native owners contribute orthogonal
-- optional structure:
--
--   * ClopenNDimFibreBoundary / TetrationalGateField:
--       local chart dimension and refinement/tower requests;
--   * RelationalBranchCobordismGeometry:
--       n-ary pants geometry and typed interface matching;
--   * ConsumerRelativeReductionCanonicalBridgeExact:
--       consumer-indexed symmetry/quotient authority;
--   * TypedHyperfabricConsumerReductionBridgeExact:
--       Set-sized selected-section codes realized as compatible GlobalSections
--       before entering the Set-sized consumer-reduction kernel;
--   * MaleCNSTypedHyperfabricChartProjectionExact:
--       26-region ordered-pair chart projection from compatible GlobalSections;
--   * braided evidence / hypercube owners:
--       path identity and presentation/transition-geometry boundaries.
--
-- The purpose here is to state the composition and its firewalls without
-- redefining FibreAt, Incidence, Transport, LocalSection or gluing semantics.
------------------------------------------------------------------------

TypedHyperfabricSurface : Set → Set → Set₁
TypedHyperfabricSurface = Hyperfabric.TypedHyperfabric

GlobalSectionSurface :
  {Vertex Edge : Set} →
  Hyperfabric.TypedHyperfabric Vertex Edge → Set₁
GlobalSectionSurface = Hyperfabric.GlobalSection

HyperfabricTraceSurface : Set → Set
HyperfabricTraceSurface = Hyperfabric.HyperfabricTrace

------------------------------------------------------------------------
-- Role assignment: which existing owner is authoritative for which operation.
------------------------------------------------------------------------

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
  "DASHI.Reasoning.TypedHyperfabricCore.restrict"
  "DASHI.Reasoning.TypedHyperfabricCore.GlobalSection.compatible"
  "DASHI.Topology.TetrationalGateField.TransitionKind (local requested transition)"
  "DASHI.Topology.ClopenNDimFibreBoundary.ClopenBallDescriptor / FiniteFibreAt"
  "DASHI.Topology.TetrationalGateField.TowerTransition"
  "DASHI.Reasoning.RelationalBranchCobordismGeometry.InterfaceMatch / composeAt"
  "DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact"
  "DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact.ConsumerInvisibleSymmetry"
  "DASHI.Biology.TernaryHypercubeHyperfabricExact (carrier/transition-geometry separation)"
  "The local-fibre architecture is a composition of already-owned theorem surfaces. TypedHyperfabric owns compatible GlobalSections in Set₁; a declared Set-sized selected-section code realizes into those sections before consumer reduction. The MaleCNS 26-region ordered-pair chart is a GlobalSection projection, while the nonzero physical connectome incidence remains a separate unpaid obligation."

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

pantsOutputMultiplicityIsLocal : Pants.outputCount Pants.composedOneToThree ≡ 3
pantsOutputMultiplicityIsLocal = Pants.composedOutputCountIsThree

pantsPathSensitiveSplitCanConserveCapacity :
  Pants.CapacityConservative Pants.phaseChangedJunction
pantsPathSensitiveSplitCanConserveCapacity =
  Pants.phaseChangedCapacityConservative

braidCrossingRetainsIdentity :
  Braid.coordinationWithoutFusion Braid.canonicalBraidedEvidenceBoundary ≡ true
braidCrossingRetainsIdentity = refl

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
  false
  false
  false
  true
  true
  false
  true
  false
  "TypedHyperfabricConsumerReductionBridgeExact now pays the universe-correct selected-section-code -> consumer-relative reduction seam without coercing GlobalSection : Set₁ into Fine : Set. MaleCNSTypedHyperfabricChartProjectionExact pays the projection of compatible GlobalSections into the 26-region ordered-pair chart. Remaining work is NDim refinement, pants seams, braid transport, an actual nonzero/typed MaleCNS physical incidence instance, and a concrete Set-sized MaleCNS selected-section carrier feeding the reduction bridge."
