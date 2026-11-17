module DASHI.Moonshine.Base369Ternary27CharacterAdjacencyEquivarianceExact where

------------------------------------------------------------------------
-- C3^3 CHARACTER EVALUATION / GRID-SYMMETRY EQUIVARIANCE
--
-- A 27-point ternary voxel has three independent C3 coordinates.  This owner
-- constructs the tensor character value directly from the already checked
-- depth-one C3 Fourier rows and proves that the geometric coordinate
-- permutations preserve nearest-neighbour adjacency.
--
-- IMPORTANT GROUP BOUNDARY:
--   C3 × C3 × C3  !=  Z/27Z.
-- They have the same cardinality 27 but different group structure.  The
-- repository's TriadicFiniteIrrep depth-three quotient is therefore not used
-- as if it were the voxel product group.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Bridge
import DASHI.Moonshine.Monster3BPhaseTransportExact as Monster

------------------------------------------------------------------------
-- 1. Exact tensor character value on C3^3.
------------------------------------------------------------------------

rowAtTrit : Fourier.FourierRow → SSP.SSPTrit → Characters.C3Phase
rowAtTrit row SSP.sspNegOne = Fourier.at2 row
rowAtTrit row SSP.sspZero = Fourier.at0 row
rowAtTrit row SSP.sspPosOne = Fourier.at1 row

axisCharacterValue : Bridge.AxisFrequency → SSP.SSPTrit → Characters.C3Phase
axisCharacterValue frequency trit = rowAtTrit (Bridge.frequencyRow frequency) trit

cubeCharacterValue :
  Bridge.CubeFrequencySector → Geometry.Ternary27Point → Characters.C3Phase
cubeCharacterValue
  (Bridge.cubeFrequencySector fx fy fz)
  (Geometry.ternary27Point x y z) =
  Characters.multiplyPhase
    (axisCharacterValue fx x)
    (Characters.multiplyPhase
      (axisCharacterValue fy y)
      (axisCharacterValue fz z))

trivialAxisCharacter :
  (t : SSP.SSPTrit) →
  axisCharacterValue Bridge.frequencyZero t ≡ Characters.phase0
trivialAxisCharacter SSP.sspNegOne = refl
trivialAxisCharacter SSP.sspZero = refl
trivialAxisCharacter SSP.sspPosOne = refl

trivialCubeCharacter :
  (p : Geometry.Ternary27Point) →
  cubeCharacterValue Bridge.trivialCubeSector p ≡ Characters.phase0
trivialCubeCharacter (Geometry.ternary27Point x y z)
  rewrite trivialAxisCharacter x
        | trivialAxisCharacter y
        | trivialAxisCharacter z = refl

------------------------------------------------------------------------
-- 2. Exact phase-product commutations needed for coordinate permutation.
------------------------------------------------------------------------

swapFirstTwoProduct :
  (a b c : Characters.C3Phase) →
  Characters.multiplyPhase b (Characters.multiplyPhase a c)
  ≡ Characters.multiplyPhase a (Characters.multiplyPhase b c)
swapFirstTwoProduct Characters.phase0 Characters.phase0 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase0 Characters.phase0 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase0 Characters.phase0 Characters.phase2 = refl
swapFirstTwoProduct Characters.phase0 Characters.phase1 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase0 Characters.phase1 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase0 Characters.phase1 Characters.phase2 = refl
swapFirstTwoProduct Characters.phase0 Characters.phase2 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase0 Characters.phase2 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase0 Characters.phase2 Characters.phase2 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase0 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase0 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase0 Characters.phase2 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase1 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase1 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase1 Characters.phase2 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase2 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase2 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase1 Characters.phase2 Characters.phase2 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase0 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase0 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase0 Characters.phase2 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase1 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase1 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase1 Characters.phase2 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase2 Characters.phase0 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase2 Characters.phase1 = refl
swapFirstTwoProduct Characters.phase2 Characters.phase2 Characters.phase2 = refl

rotateProduct :
  (a b c : Characters.C3Phase) →
  Characters.multiplyPhase b (Characters.multiplyPhase c a)
  ≡ Characters.multiplyPhase a (Characters.multiplyPhase b c)
rotateProduct Characters.phase0 Characters.phase0 Characters.phase0 = refl
rotateProduct Characters.phase0 Characters.phase0 Characters.phase1 = refl
rotateProduct Characters.phase0 Characters.phase0 Characters.phase2 = refl
rotateProduct Characters.phase0 Characters.phase1 Characters.phase0 = refl
rotateProduct Characters.phase0 Characters.phase1 Characters.phase1 = refl
rotateProduct Characters.phase0 Characters.phase1 Characters.phase2 = refl
rotateProduct Characters.phase0 Characters.phase2 Characters.phase0 = refl
rotateProduct Characters.phase0 Characters.phase2 Characters.phase1 = refl
rotateProduct Characters.phase0 Characters.phase2 Characters.phase2 = refl
rotateProduct Characters.phase1 Characters.phase0 Characters.phase0 = refl
rotateProduct Characters.phase1 Characters.phase0 Characters.phase1 = refl
rotateProduct Characters.phase1 Characters.phase0 Characters.phase2 = refl
rotateProduct Characters.phase1 Characters.phase1 Characters.phase0 = refl
rotateProduct Characters.phase1 Characters.phase1 Characters.phase1 = refl
rotateProduct Characters.phase1 Characters.phase1 Characters.phase2 = refl
rotateProduct Characters.phase1 Characters.phase2 Characters.phase0 = refl
rotateProduct Characters.phase1 Characters.phase2 Characters.phase1 = refl
rotateProduct Characters.phase1 Characters.phase2 Characters.phase2 = refl
rotateProduct Characters.phase2 Characters.phase0 Characters.phase0 = refl
rotateProduct Characters.phase2 Characters.phase0 Characters.phase1 = refl
rotateProduct Characters.phase2 Characters.phase0 Characters.phase2 = refl
rotateProduct Characters.phase2 Characters.phase1 Characters.phase0 = refl
rotateProduct Characters.phase2 Characters.phase1 Characters.phase1 = refl
rotateProduct Characters.phase2 Characters.phase1 Characters.phase2 = refl
rotateProduct Characters.phase2 Characters.phase2 Characters.phase0 = refl
rotateProduct Characters.phase2 Characters.phase2 Characters.phase1 = refl
rotateProduct Characters.phase2 Characters.phase2 Characters.phase2 = refl

characterSwapCovariance :
  (s : Bridge.CubeFrequencySector) →
  (p : Geometry.Ternary27Point) →
  cubeCharacterValue (Bridge.swapSectorXY s) (Bridge.swapXY p)
  ≡ cubeCharacterValue s p
characterSwapCovariance
  (Bridge.cubeFrequencySector fx fy fz)
  (Geometry.ternary27Point x y z) =
  swapFirstTwoProduct
    (axisCharacterValue fx x)
    (axisCharacterValue fy y)
    (axisCharacterValue fz z)

characterRotationCovariance :
  (s : Bridge.CubeFrequencySector) →
  (p : Geometry.Ternary27Point) →
  cubeCharacterValue (Bridge.rotateSectorXYZ s) (Bridge.rotateXYZ p)
  ≡ cubeCharacterValue s p
characterRotationCovariance
  (Bridge.cubeFrequencySector fx fy fz)
  (Geometry.ternary27Point x y z) =
  rotateProduct
    (axisCharacterValue fx x)
    (axisCharacterValue fy y)
    (axisCharacterValue fz z)

------------------------------------------------------------------------
-- 3. Coordinate permutations are automorphisms of the nearest-neighbour graph.
------------------------------------------------------------------------

swapPreservesAdjacency :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q →
  Geometry.HypervoxelAdjacent (Bridge.swapXY p) (Bridge.swapXY q)
swapPreservesAdjacency (Geometry.adjacentX step) = Geometry.adjacentY step
swapPreservesAdjacency (Geometry.adjacentY step) = Geometry.adjacentX step
swapPreservesAdjacency (Geometry.adjacentZ step) = Geometry.adjacentZ step

rotatePreservesAdjacency :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q →
  Geometry.HypervoxelAdjacent (Bridge.rotateXYZ p) (Bridge.rotateXYZ q)
rotatePreservesAdjacency (Geometry.adjacentX step) = Geometry.adjacentZ step
rotatePreservesAdjacency (Geometry.adjacentY step) = Geometry.adjacentX step
rotatePreservesAdjacency (Geometry.adjacentZ step) = Geometry.adjacentY step

------------------------------------------------------------------------
-- 4. Character conjugation and Monster 3B inversion share the existing exact
--    phase intertwiner; this remains a phase-level bridge only.
------------------------------------------------------------------------

axisCharacterConjugation :
  (f : Bridge.AxisFrequency) →
  (t : SSP.SSPTrit) →
  Characters.conjugatePhase (axisCharacterValue f t)
  ≡ axisCharacterValue (Bridge.conjugateFrequency f) t
axisCharacterConjugation Bridge.frequencyZero SSP.sspNegOne = refl
axisCharacterConjugation Bridge.frequencyZero SSP.sspZero = refl
axisCharacterConjugation Bridge.frequencyZero SSP.sspPosOne = refl
axisCharacterConjugation Bridge.frequencyPositive SSP.sspNegOne = refl
axisCharacterConjugation Bridge.frequencyPositive SSP.sspZero = refl
axisCharacterConjugation Bridge.frequencyPositive SSP.sspPosOne = refl
axisCharacterConjugation Bridge.frequencyNegative SSP.sspNegOne = refl
axisCharacterConjugation Bridge.frequencyNegative SSP.sspZero = refl
axisCharacterConjugation Bridge.frequencyNegative SSP.sspPosOne = refl

monsterAxisConjugationIntertwines :
  (f : Bridge.AxisFrequency) →
  (t : SSP.SSPTrit) →
  Fourier.phaseToMonster (axisCharacterValue (Bridge.conjugateFrequency f) t)
  ≡ Monster.transportPhase Monster.invertsGenerator
      (Fourier.phaseToMonster (axisCharacterValue f t))
monsterAxisConjugationIntertwines f t
  rewrite <- axisCharacterConjugation f t =
  Fourier.monsterInversionIntertwinesConjugation (axisCharacterValue f t)

------------------------------------------------------------------------
-- 5. Product-group / cyclic-group non-collapse boundary.
------------------------------------------------------------------------

record ProductC3VsCyclic27Boundary : Set where
  constructor productC3VsCyclic27Boundary
  field
    sameCardinality : Bool
    sameGroupClaimed : Bool
    depthOneCharactersCanTensorIndexVoxel : Bool
    depthThreeCyclicIrrepUsedAsVoxelIrrepWithoutBridge : Bool

canonicalProductC3VsCyclic27Boundary : ProductC3VsCyclic27Boundary
canonicalProductC3VsCyclic27Boundary =
  productC3VsCyclic27Boundary true false true false

record Ternary27CharacterAdjacencyBoundary : Set where
  constructor ternary27CharacterAdjacencyBoundary
  field
    tensorCharacterEvaluationConstructed : Bool
    trivialSectorConstant : Bool
    swapCharacterCovariant : Bool
    rotationCharacterCovariant : Bool
    swapPreservesGridAdjacency : Bool
    rotationPreservesGridAdjacency : Bool
    monsterConjugationIntertwinesAxisCharacter : Bool
    adjacencySpectrumComputedHere : Bool
    graphLaplacianDiagonalisedHere : Bool
    monsterRepresentationEstablishedHere : Bool

canonicalTernary27CharacterAdjacencyBoundary : Ternary27CharacterAdjacencyBoundary
canonicalTernary27CharacterAdjacencyBoundary =
  ternary27CharacterAdjacencyBoundary
    true true true true true true true false false false
