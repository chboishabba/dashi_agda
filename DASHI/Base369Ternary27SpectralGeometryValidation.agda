module DASHI.Base369Ternary27SpectralGeometryValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Stratification
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as Symmetry
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.Base369Ternary27CharacterAdjacencyEquivarianceExact as Character
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed

oneVoxelHas27States : Geometry.hypervoxelStateCount ≡ 27
oneVoxelHas27States = Geometry.hypervoxelStateCountIs27

appraisalFibreHas729States : Geometry.appraisalFibreStateCount ≡ 729
appraisalFibreHas729States = Geometry.appraisalFibreStateCountIs729

threeVoxelFabricHas19683States : Geometry.hyperfabricStateCount ≡ 19683
threeVoxelFabricHas19683States = Geometry.hyperfabricStateCountIs19683

originStabiliserIsS3 : Spectral.voxelStabiliser Geometry.origin ≡ Symmetry.fullStabiliserS3
originStabiliserIsS3 = Spectral.originHasFullS3

axisPointStabiliserIsS2 :
  Spectral.voxelStabiliser Spectral.onePositiveAxisPoint ≡ Symmetry.pairStabiliserS2
axisPointStabiliserIsS2 = Spectral.onePositiveAxisPointHasS2

allDistinctStabiliserIsTrivial :
  Spectral.voxelStabiliser Spectral.threeDistinctPoint ≡ Symmetry.trivialStabiliser
allDistinctStabiliserIsTrivial = Spectral.threeDistinctPointHasTrivialStabiliser

coordinateRotationHasOrderThree :
  (p : Geometry.Ternary27Point) →
  Spectral.rotateXYZ (Spectral.rotateXYZ (Spectral.rotateXYZ p)) ≡ p
coordinateRotationHasOrderThree = Spectral.rotateXYZOrderThree

xReflectionIsInvolution :
  (p : Geometry.Ternary27Point) → Signed.flipX (Signed.flipX p) ≡ p
xReflectionIsInvolution = Signed.flipXInvolutive

xReflectionPreservesGrid :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q →
  Geometry.HypervoxelAdjacent (Signed.flipX p) (Signed.flipX q)
xReflectionPreservesGrid = Signed.flipXPreservesAdjacency

coordinateSwapPreservesGrid :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q →
  Geometry.HypervoxelAdjacent (Spectral.swapXY p) (Spectral.swapXY q)
coordinateSwapPreservesGrid = Character.swapPreservesAdjacency

cubeFrequencySectorCountIs27 : Spectral.cubeSectorCount ≡ 27
cubeFrequencySectorCountIs27 = Spectral.cubeSectorCountIs27

hyperfabricFrequencySectorCountIs19683 : Spectral.hyperfabricSectorCount ≡ 19683
hyperfabricFrequencySectorCountIs19683 = Spectral.hyperfabricSectorCountIs19683

trivialCharacterConstant :
  (p : Geometry.Ternary27Point) →
  Character.cubeCharacterValue Spectral.trivialCubeSector p ≡ Characters.phase0
trivialCharacterConstant = Character.trivialCubeCharacter

c3CubedNotClaimedAsCyclic27 :
  Character.ProductC3VsCyclic27Boundary.sameGroupClaimed
    Character.canonicalProductC3VsCyclic27Boundary ≡ false
c3CubedNotClaimedAsCyclic27 = refl

depthThreeCyclicIrrepNotSilentlyUsed :
  Character.ProductC3VsCyclic27Boundary.depthThreeCyclicIrrepUsedAsVoxelIrrepWithoutBridge
    Character.canonicalProductC3VsCyclic27Boundary ≡ false
depthThreeCyclicIrrepNotSilentlyUsed = refl

fullDFTNotClaimed :
  Spectral.Base369Ternary27SpectralSymmetryBoundary.fullTwentySevenPointDFTConstructed
    Spectral.canonicalBase369Ternary27SpectralSymmetryBoundary ≡ false
fullDFTNotClaimed = refl

laplacianDiagonalisationNotClaimed :
  Character.Ternary27CharacterAdjacencyBoundary.graphLaplacianDiagonalisedHere
    Character.canonicalTernary27CharacterAdjacencyBoundary ≡ false
laplacianDiagonalisationNotClaimed = refl

monsterRepresentationNotClaimed :
  Signed.SignedTernaryVoxelSymmetryBoundary.voxelRepresentationOfMonsterEstablished
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary ≡ false
monsterRepresentationNotClaimed = refl

monsterEmbeddingNotClaimed :
  Signed.SignedTernaryVoxelSymmetryBoundary.signedPermutationGroupEmbeddedInMonster
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary ≡ false
monsterEmbeddingNotClaimed = refl

monsterPhaseIntertwinerPinned :
  Signed.SignedTernaryVoxelSymmetryBoundary.monster3BPhaseInversionMatchesFrequencyConjugation
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary ≡ true
monsterPhaseIntertwinerPinned = refl
