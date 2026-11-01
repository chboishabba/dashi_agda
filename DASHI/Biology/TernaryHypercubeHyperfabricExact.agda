module DASHI.Biology.TernaryHypercubeHyperfabricExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact finite cardinality spine for binary vertices, ternary lattice points,
-- oriented-zero refinements, sheets, voxels, and higher hyperfabric carriers.

powNat : Nat → Nat → Nat
powNat base zero = 1
powNat base (suc n) = base * powNat base n

binaryVertexCount : Nat → Nat
binaryVertexCount = powNat 2

ternaryLatticeCount : Nat → Nat
ternaryLatticeCount = powNat 3

orientedZeroMicrostateCount : Nat → Nat
orientedZeroMicrostateCount = powNat 4

binaryCubeThreeHasEightVertices : binaryVertexCount 3 ≡ 8
binaryCubeThreeHasEightVertices = refl

ternaryCubeThreeHasTwentySevenLatticePoints :
  ternaryLatticeCount 3 ≡ 27
ternaryCubeThreeHasTwentySevenLatticePoints = refl

ternaryNineSheetHasNineteenThousandSixHundredEightyThreeStates :
  ternaryLatticeCount 9 ≡ 19683
ternaryNineSheetHasNineteenThousandSixHundredEightyThreeStates = refl

orientedNineSheetHasTwoHundredSixtyTwoThousandOneHundredFortyFourMicrostates :
  orientedZeroMicrostateCount 9 ≡ 262144
orientedNineSheetHasTwoHundredSixtyTwoThousandOneHundredFortyFourMicrostates = refl

------------------------------------------------------------------------
-- The same carrier set admits distinct transition geometries.

data TernaryTransitionGeometry : Set where
  mediatedPathGeometry : TernaryTransitionGeometry
  unrestrictedHammingGeometry : TernaryTransitionGeometry
  cyclicPhaseGeometry : TernaryTransitionGeometry

allowsDirectPoleJump : TernaryTransitionGeometry → Bool
allowsDirectPoleJump mediatedPathGeometry = false
allowsDirectPoleJump unrestrictedHammingGeometry = true
allowsDirectPoleJump cyclicPhaseGeometry = true

mediatedGeometryBlocksDirectPoleJump :
  allowsDirectPoleJump mediatedPathGeometry ≡ false
mediatedGeometryBlocksDirectPoleJump = refl

------------------------------------------------------------------------
-- DASHI positional scales.

data CarrierScale : Set where
  lineThree : CarrierScale
  sheetThreeByThree : CarrierScale
  sheetThreeByNine : CarrierScale
  sheetSixByNine : CarrierScale
  sheetNineByNine : CarrierScale
  voxelNineByNineByThree : CarrierScale
  blockNineCubedByThree : CarrierScale

siteCount : CarrierScale → Nat
siteCount lineThree = 3
siteCount sheetThreeByThree = 9
siteCount sheetThreeByNine = 27
siteCount sheetSixByNine = 54
siteCount sheetNineByNine = 81
siteCount voxelNineByNineByThree = 243
siteCount blockNineCubedByThree = 2187

siteCountThreeByNineIsTwentySeven : siteCount sheetThreeByNine ≡ 27
siteCountThreeByNineIsTwentySeven = refl

siteCountSixByNineIsFiftyFour : siteCount sheetSixByNine ≡ 54
siteCountSixByNineIsFiftyFour = refl

siteCountNineByNineIsEightyOne : siteCount sheetNineByNine ≡ 81
siteCountNineByNineIsEightyOne = refl

siteCountNineByNineByThreeIsTwoHundredFortyThree :
  siteCount voxelNineByNineByThree ≡ 243
siteCountNineByNineByThreeIsTwoHundredFortyThree = refl

configurationCount : CarrierScale → Nat
configurationCount scale = ternaryLatticeCount (siteCount scale)

------------------------------------------------------------------------
-- Product growth and genuine fixed-base tetration are distinct recursions.

productTowerSites : Nat → Nat
productTowerSites zero = 9
productTowerSites (suc n) = 9 * productTowerSites n

nineTetration : Nat → Nat
nineTetration zero = 1
nineTetration (suc n) = powNat 9 (nineTetration n)

firstNineTetrationLevel : nineTetration 1 ≡ 9
firstNineTetrationLevel = refl

nineTetrationRecurrence :
  (n : Nat) → nineTetration (suc n) ≡ powNat 9 (nineTetration n)
nineTetrationRecurrence n = refl

------------------------------------------------------------------------
-- Hypercube / hypervoxel / hyperfabric typing.

data GeometricCarrierKind : Set where
  hypercubeVertexCarrier : GeometricCarrierKind
  stratifiedHypervoxelCarrier : GeometricCarrierKind
  transportedHyperfabricCarrier : GeometricCarrierKind

record HypervoxelCell : Set where
  constructor hypervoxelCell
  field
    scale : CarrierScale
    localStateCount : Nat
    residualDepth : Nat
    pathMemoryDepth : Nat

open HypervoxelCell public

canonicalNineCell : HypervoxelCell
canonicalNineCell =
  hypervoxelCell sheetThreeByThree 19683 1 1

data TransitionKind : Set where
  objectLevelAdmissible : TransitionKind
  typedRegimeTransition : TransitionKind
  explicitViolationWitness : TransitionKind

record PrincipledFibreTransition : Set where
  constructor principledFibreTransition
  field
    sourceScale : CarrierScale
    targetScale : CarrierScale
    kind : TransitionKind
    preservesDeclaredCarrierType : Bool
    preservesResidualWitness : Bool

open PrincipledFibreTransition public

canonicalRefinementTransition : PrincipledFibreTransition
canonicalRefinementTransition =
  principledFibreTransition
    sheetThreeByThree
    sheetThreeByNine
    typedRegimeTransition
    true
    true

record HyperfabricBoundary : Set where
  constructor hyperfabricBoundary
  field
    ternaryCarrierIsOnlyHypercubeVertices : Bool
    ternaryCarrierIsOnlyHypercubeVerticesIsFalse :
      ternaryCarrierIsOnlyHypercubeVertices ≡ false

    everySyntacticJumpIsObjectLevelAdmissible : Bool
    everySyntacticJumpIsObjectLevelAdmissibleIsFalse :
      everySyntacticJumpIsObjectLevelAdmissible ≡ false

    productExtensionIsAutomaticallyTetration : Bool
    productExtensionIsAutomaticallyTetrationIsFalse :
      productExtensionIsAutomaticallyTetration ≡ false

    violationWitnessIsSameAsUnlicensedTransition : Bool
    violationWitnessIsSameAsUnlicensedTransitionIsFalse :
      violationWitnessIsSameAsUnlicensedTransition ≡ false

open HyperfabricBoundary public

canonicalHyperfabricBoundary : HyperfabricBoundary
canonicalHyperfabricBoundary =
  hyperfabricBoundary false refl false refl false refl false refl
