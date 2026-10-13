module DASHI.Biology.IIT369PantsGluingBridgeExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.Base369FiniteRingLaws as Ring369
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Cobordism
import DASHI.Topology.TernaryCylinderPantsGeometryExact as PantsGeometry
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

------------------------------------------------------------------------
-- 369 / TERNARY PANTS / IIT COMPOSITION BRIDGE
--
-- Existing repository owners already distinguish:
--   * ternary algebra (TriTruth = F3 under triXor + multiplication),
--   * nonary cyclic algebra (NonaryTruth = Z/9Z-like ring carrier),
--   * nine-sheet/product coordinates,
--   * a canonical finite 1 -> 3 pants junction,
--   * arbitrary-depth ternary pants paths,
--   * exact nine-sheet <-> depth-2 and 27-voxel <-> depth-3 pants charts.
--
-- This module does not identify any of those objects with IIT integrated
-- information.  It exposes them as independent causal-mechanism coordinates so
-- matched IIT experiments can vary local algebra and composition geometry
-- separately.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Existing exact 1 -> 3 gluing geometry.
------------------------------------------------------------------------

canonicalPantsHasThreeOutputs :
  Cobordism.outputCount Cobordism.composedOneToThree ≡ 3
canonicalPantsHasThreeOutputs = PantsGeometry.canonicalPantsHasThreeOutputs

canonicalPantsIsCapacityConservative :
  Cobordism.CapacityConservative Cobordism.composedOneToThree
canonicalPantsIsCapacityConservative = PantsGeometry.canonicalPantsCapacityConservative

canonicalPantsIsWaveConservative :
  Cobordism.WaveConservative Cobordism.composedOneToThree
canonicalPantsIsWaveConservative = PantsGeometry.canonicalPantsWaveConservative

------------------------------------------------------------------------
-- 2. Exact finite chart equivalences already owned by the 369 lane.
------------------------------------------------------------------------

nineSheetToPants2 : Triadic.NineSheet → Frontier.PantsPath 2
nineSheetToPants2 = Pants369.nineToPants2

pants2ToNineSheet : Frontier.PantsPath 2 → Triadic.NineSheet
pants2ToNineSheet = Pants369.pants2ToNine

nineSheetPantsRoundTrip :
  (sheet : Triadic.NineSheet) →
  pants2ToNineSheet (nineSheetToPants2 sheet) ≡ sheet
nineSheetPantsRoundTrip = Pants369.ninePantsRoundTrip

pants2NineSheetRoundTrip :
  (path : Frontier.PantsPath 2) →
  nineSheetToPants2 (pants2ToNineSheet path) ≡ path
pants2NineSheetRoundTrip = Pants369.pantsNineRoundTrip

voxel27ToPants3 : Fabric.Ternary27Point → Frontier.PantsPath 3
voxel27ToPants3 = Pants369.voxel27ToPants3

pants3ToVoxel27 : Frontier.PantsPath 3 → Fabric.Ternary27Point
pants3ToVoxel27 = Pants369.pants3ToVoxel27

voxel27PantsRoundTrip :
  (voxel : Fabric.Ternary27Point) →
  pants3ToVoxel27 (voxel27ToPants3 voxel) ≡ voxel
voxel27PantsRoundTrip = Pants369.voxelPantsRoundTrip

pants3Voxel27RoundTrip :
  (path : Frontier.PantsPath 3) →
  voxel27ToPants3 (pants3ToVoxel27 path) ≡ path
pants3Voxel27RoundTrip = Pants369.pantsVoxelRoundTrip

allFiniteDepthTernaryPantsCharts :
  (n : Nat) → Frontier.FrontierEquivalence n
allFiniteDepthTernaryPantsCharts = Frontier.canonicalFrontierEquivalence

------------------------------------------------------------------------
-- 3. Local algebra and composition geometry are independent coordinates.
------------------------------------------------------------------------

data LocalAlgebraKind : Set where
  booleanXorAlgebra : LocalAlgebraKind
  triTruthFieldAlgebra : LocalAlgebraKind
  nonaryCyclicRingAlgebra : LocalAlgebraKind
  phaseProductF3SquaredAlgebra : LocalAlgebraKind

data CompositionGeometryKind : Set where
  binaryGraphComposition : CompositionGeometryKind
  ternaryOneToThreePantsComposition : CompositionGeometryKind
  ternaryDepthTwoPantsComposition : CompositionGeometryKind
  ternaryDepthThreePantsComposition : CompositionGeometryKind

record MatchedMechanismFamily : Set where
  constructor matchedMechanismFamily
  field
    localAlgebra : LocalAlgebraKind
    compositionGeometry : CompositionGeometryKind
    familyLabel : String

open MatchedMechanismFamily public

booleanXorBinaryFamily : MatchedMechanismFamily
booleanXorBinaryFamily =
  matchedMechanismFamily
    booleanXorAlgebra
    binaryGraphComposition
    "Boolean XOR on binary graph composition"

triTruthPantsFamily : MatchedMechanismFamily
triTruthPantsFamily =
  matchedMechanismFamily
    triTruthFieldAlgebra
    ternaryOneToThreePantsComposition
    "F3 / triXor on canonical 1-to-3 pants composition"

nonaryPantsFamily : MatchedMechanismFamily
nonaryPantsFamily =
  matchedMechanismFamily
    nonaryCyclicRingAlgebra
    ternaryDepthTwoPantsComposition
    "Z/9Z-like nonary ring on depth-two pants coordinates"

phaseProductPantsFamily : MatchedMechanismFamily
phaseProductPantsFamily =
  matchedMechanismFamily
    phaseProductF3SquaredAlgebra
    ternaryDepthTwoPantsComposition
    "F3^2 phase-product law on the same nine-state pants depth"

------------------------------------------------------------------------
-- 4. Exact algebra receipts reused rather than reconstructed.
------------------------------------------------------------------------

triTruthFieldReceipt : Ring369.TriTruthIsField
triTruthFieldReceipt = Ring369.triTruthFieldReceipt

nonaryRingReceipt : Ring369.RingAuthoritySlot
nonaryRingReceipt = Ring369.nonaryTruthRingAuthoritySlot

nonaryHasZeroDivisors :
  Ring369.ZeroDivisorWitness
    Base.NonaryTruth
    Base.non-0
    Ring369.nonaryTruthMul
nonaryHasZeroDivisors = Ring369.nonaryZeroDivisorWitness-3-3

------------------------------------------------------------------------
-- 5. Separation firewalls for IIT use.
------------------------------------------------------------------------

data CompositionVsAlgebraAxis : Set where
  algebraAxis : CompositionVsAlgebraAxis
  compositionAxis : CompositionVsAlgebraAxis

algebraAxisNotCompositionAxis : algebraAxis ≡ compositionAxis → ⊥
algebraAxisNotCompositionAxis ()

record IIT369PantsBoundary : Set where
  constructor iit369PantsBoundary
  field
    canonicalOneToThreePantsExists : Bool
    nineSheetDepthTwoRoundTripExists : Bool
    voxel27DepthThreeRoundTripExists : Bool
    arbitraryFiniteDepthPantsChartExists : Bool
    triTruthFieldLawOwned : Bool
    nonaryRingLawOwned : Bool
    localAlgebraEqualsCompositionGeometryByDefinition : Bool
    threeWayPantsGluingEqualsIITPhiByDefinition : Bool
    depthThreePantsPathEqualsConsciousnessByDefinition : Bool
    sameNineStateCardinalityForcesSameAlgebra : Bool
    matchedIITExperimentShouldVaryAxesSeparately : Bool

open IIT369PantsBoundary public

canonicalIIT369PantsBoundary : IIT369PantsBoundary
canonicalIIT369PantsBoundary =
  iit369PantsBoundary
    true true true true true true
    false false false false true

pantsGluingDoesNotSelfPromoteToPhi :
  threeWayPantsGluingEqualsIITPhiByDefinition canonicalIIT369PantsBoundary ≡ false
pantsGluingDoesNotSelfPromoteToPhi = refl

algebraAndGeometryRemainIndependent :
  localAlgebraEqualsCompositionGeometryByDefinition canonicalIIT369PantsBoundary ≡ false
algebraAndGeometryRemainIndependent = refl

sameNineStatesDoNotForceSameAlgebra :
  sameNineStateCardinalityForcesSameAlgebra canonicalIIT369PantsBoundary ≡ false
sameNineStatesDoNotForceSameAlgebra = refl
