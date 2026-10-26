module DASHI.Biology.IIT369PantsGluingBridgeExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.Base369FiniteRingLaws as Ring369
import DASHI.Foundations.HexTruthS3CarrierBridgeExact as HexS3
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Cobordism
import DASHI.Reasoning.TernaryPantsSynthesisS3BridgeExact as PantsS3
import DASHI.Reasoning.TrialecticThreeCellCarryDepthExact as Trialectic
import DASHI.Topology.TernaryCylinderPantsGeometryExact as PantsGeometry
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

------------------------------------------------------------------------
-- 369 / TERNARY PANTS / IIT COMPOSITION BRIDGE
--
-- 369 is not treated merely as the cardinality tower 3,9,27.  Existing repo
-- owners supply several genuinely different algebraic lenses:
--
--   * TriTruth ~ F3 under triXor + multiplication,
--   * HexTruth ~ cyclic Z/6Z-like addition/ring carrier,
--   * the same six-state carrier charted to noncommutative S3 permutations,
--   * NonaryTruth ~ Z/9Z-like cyclic ring carrier,
--   * Q9 ~ F3^2 componentwise addition,
--   * exact nine-sheet / 27-voxel ternary composition charts,
--   * canonical finite 1 -> 3 pants and recursive S3 actions.
--
-- IIT sees these only through an explicitly chosen causal transition system.
-- Algebra, carrier chart, and composition geometry remain separate axes.
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
-- 3. Existing higher-order three-way synthesis surfaces.
------------------------------------------------------------------------

recursivePantsS3Boundary : PantsS3.TernaryPantsSynthesisS3Boundary
recursivePantsS3Boundary = PantsS3.canonicalTernaryPantsSynthesisS3Boundary

trialecticCarryDepthBoundary : Trialectic.TrialecticThreeCellCarryDepthBoundary
trialecticCarryDepthBoundary = Trialectic.canonicalTrialecticThreeCellCarryDepthBoundary

recursivePantsSupportsLocal27AtEveryParent :
  PantsS3.TernaryPantsSynthesisS3Boundary.local27CellAttachedAtEveryParent
    recursivePantsS3Boundary ≡ true
recursivePantsSupportsLocal27AtEveryParent = refl

trialecticPromotionKeepsLowerStructuredState :
  Trialectic.TrialecticThreeCellCarryDepthBoundary.lowerStructuredTrialecticRetained
    trialecticCarryDepthBoundary ≡ true
trialecticPromotionKeepsLowerStructuredState = refl

trialecticFaceMediationIsNotAutomatic :
  Trialectic.TrialecticThreeCellCarryDepthBoundary.concreteFaceMediationDerivedAutomatically
    trialecticCarryDepthBoundary ≡ false
trialecticFaceMediationIsNotAutomatic = refl

------------------------------------------------------------------------
-- 4. Local algebra and composition geometry are independent coordinates.
------------------------------------------------------------------------

data LocalAlgebraKind : Set where
  booleanXorAlgebra : LocalAlgebraKind
  triTruthFieldAlgebra : LocalAlgebraKind
  hexTruthCyclicRingAlgebra : LocalAlgebraKind
  s3PermutationAlgebra : LocalAlgebraKind
  nonaryCyclicRingAlgebra : LocalAlgebraKind
  phaseProductF3SquaredAlgebra : LocalAlgebraKind

data CompositionGeometryKind : Set where
  binaryGraphComposition : CompositionGeometryKind
  ternaryOneToThreePantsComposition : CompositionGeometryKind
  ternaryDepthTwoPantsComposition : CompositionGeometryKind
  ternaryDepthThreePantsComposition : CompositionGeometryKind
  trialecticSecondOrderFaceComposition : CompositionGeometryKind

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

hexTruthBinaryFamily : MatchedMechanismFamily
hexTruthBinaryFamily =
  matchedMechanismFamily
    hexTruthCyclicRingAlgebra
    binaryGraphComposition
    "Z/6Z-like HexTruth cyclic law on matched graph composition"

s3BinaryFamily : MatchedMechanismFamily
s3BinaryFamily =
  matchedMechanismFamily
    s3PermutationAlgebra
    binaryGraphComposition
    "noncommutative S3 permutation product on the same six-state carrier/fabric"

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

triTruthTrialecticFaceFamily : MatchedMechanismFamily
triTruthTrialecticFaceFamily =
  matchedMechanismFamily
    triTruthFieldAlgebra
    trialecticSecondOrderFaceComposition
    "F3 local algebra with explicit second-order three-edge face mediation"

------------------------------------------------------------------------
-- 5. Exact algebra receipts reused rather than reconstructed.
------------------------------------------------------------------------

triTruthFieldReceipt : Ring369.TriTruthIsField
triTruthFieldReceipt = Ring369.triTruthFieldReceipt

hexTruthRingReceipt : Ring369.RingAuthoritySlot
hexTruthRingReceipt = Ring369.hexTruthRingAuthoritySlot

hexTruthHasZeroDivisors :
  Ring369.ZeroDivisorWitness
    Base.HexTruth
    Base.hex-0
    Ring369.hexTruthMul
hexTruthHasZeroDivisors = Ring369.hexZeroDivisorWitness

hexS3CarrierRoundTrip :
  (hex : Base.HexTruth) →
  HexS3.permutationToHex (HexS3.hexToPermutation hex) ≡ hex
hexS3CarrierRoundTrip = HexS3.hexRoundTrip

hexS3ProductsRemainDistinct :
  ((left right : Base.HexTruth) →
    HexS3.hexToPermutation (Base.hexXor left right)
    ≡ S3._∙_ (HexS3.hexToPermutation left) (HexS3.hexToPermutation right)) →
  ⊥
hexS3ProductsRemainDistinct = HexS3.hexCarrierChartCannotPreserveBothProducts

nonaryRingReceipt : Ring369.RingAuthoritySlot
nonaryRingReceipt = Ring369.nonaryTruthRingAuthoritySlot

nonaryHasZeroDivisors :
  Ring369.ZeroDivisorWitness
    Base.NonaryTruth
    Base.non-0
    Ring369.nonaryTruthMul
nonaryHasZeroDivisors = Ring369.nonaryZeroDivisorWitness-3-3

------------------------------------------------------------------------
-- 6. Separation firewalls for IIT use.
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
    recursiveThreeChildSynthesisExists : Bool
    secondOrderTrialecticFaceGluingTyped : Bool
    triTruthFieldLawOwned : Bool
    hexTruthRingLawOwned : Bool
    hexTruthS3CarrierChartOwned : Bool
    nonaryRingLawOwned : Bool
    localAlgebraEqualsCompositionGeometryByDefinition : Bool
    hexTruthProductEqualsS3ProductByDefinition : Bool
    pairwiseCompatibilityDeterminesTriadicFaceByDefinition : Bool
    threeWayPantsGluingEqualsIITPhiByDefinition : Bool
    depthThreePantsPathEqualsConsciousnessByDefinition : Bool
    sameNineStateCardinalityForcesSameAlgebra : Bool
    matchedIITExperimentShouldVaryAxesSeparately : Bool

open IIT369PantsBoundary public

canonicalIIT369PantsBoundary : IIT369PantsBoundary
canonicalIIT369PantsBoundary =
  iit369PantsBoundary
    true true true true true true true true true true
    false false false false false false true

pantsGluingDoesNotSelfPromoteToPhi :
  threeWayPantsGluingEqualsIITPhiByDefinition canonicalIIT369PantsBoundary ≡ false
pantsGluingDoesNotSelfPromoteToPhi = refl

hexTruthAndS3RemainDistinct :
  hexTruthProductEqualsS3ProductByDefinition canonicalIIT369PantsBoundary ≡ false
hexTruthAndS3RemainDistinct = refl

pairwiseCompatibilityDoesNotManufactureTriadicFace :
  pairwiseCompatibilityDeterminesTriadicFaceByDefinition canonicalIIT369PantsBoundary ≡ false
pairwiseCompatibilityDoesNotManufactureTriadicFace = refl

algebraAndGeometryRemainIndependent :
  localAlgebraEqualsCompositionGeometryByDefinition canonicalIIT369PantsBoundary ≡ false
algebraAndGeometryRemainIndependent = refl

sameNineStatesDoNotForceSameAlgebra :
  sameNineStateCardinalityForcesSameAlgebra canonicalIIT369PantsBoundary ≡ false
sameNineStatesDoNotForceSameAlgebra = refl
