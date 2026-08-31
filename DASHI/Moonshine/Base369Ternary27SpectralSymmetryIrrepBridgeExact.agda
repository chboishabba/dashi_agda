module DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact where

------------------------------------------------------------------------
-- BASE369 / 27-HYPERVOXEL / C3 SPECTRAL-SYMMETRY BRIDGE
--
-- The 27-point ternary cube is the product of three three-point carriers.
-- Existing repository owners already provide:
--   * SSPTrit = {-1,0,+1}
--   * exact Z/3Z depth-one characters and symbolic C3 phases
--   * C3 Fourier rows and conjugation
--   * S3/S2/trivial stabiliser classification of ternary triads
--   * a Monster 3B phase-inversion intertwiner
--
-- This file composes those exact surfaces.  It does NOT claim that the
-- 27-hypervoxel is a Monster representation, that a full 27-point DFT has been
-- constructed, or that an arbitrary hyperfabric operator is Schur-diagonal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as Symmetry
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Algebra.TriadicFiniteIrrep as Irrep
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Governance.HyperformalTernaryCarrierEquivalenceExact as Carrier
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Exact SSP -> balanced-digit chart for geometric symmetry classification.
------------------------------------------------------------------------

sspToBalanced : SSP.SSPTrit → Symmetry.BalancedDigit
sspToBalanced SSP.sspNegOne = Symmetry.neg
sspToBalanced SSP.sspZero = Symmetry.zeroDigit
sspToBalanced SSP.sspPosOne = Symmetry.pos

balancedToSSP : Symmetry.BalancedDigit → SSP.SSPTrit
balancedToSSP Symmetry.neg = SSP.sspNegOne
balancedToSSP Symmetry.zeroDigit = SSP.sspZero
balancedToSSP Symmetry.pos = SSP.sspPosOne

sspBalancedRoundTrip : (t : SSP.SSPTrit) → balancedToSSP (sspToBalanced t) ≡ t
sspBalancedRoundTrip SSP.sspNegOne = refl
sspBalancedRoundTrip SSP.sspZero = refl
sspBalancedRoundTrip SSP.sspPosOne = refl

balancedSSPRoundTrip : (d : Symmetry.BalancedDigit) → sspToBalanced (balancedToSSP d) ≡ d
balancedSSPRoundTrip Symmetry.neg = refl
balancedSSPRoundTrip Symmetry.zeroDigit = refl
balancedSSPRoundTrip Symmetry.pos = refl

voxelPattern : Geometry.Ternary27Point → Symmetry.TriadPattern
voxelPattern (Geometry.ternary27Point x y z) =
  Symmetry.triad (sspToBalanced x) (sspToBalanced y) (sspToBalanced z)

voxelStabiliser : Geometry.Ternary27Point → Symmetry.StabiliserType
voxelStabiliser p = Symmetry.patternStabiliser (voxelPattern p)

originHasFullS3 : voxelStabiliser Geometry.origin ≡ Symmetry.fullStabiliserS3
originHasFullS3 = refl

positiveCornerHasFullS3 : voxelStabiliser Geometry.positiveCorner ≡ Symmetry.fullStabiliserS3
positiveCornerHasFullS3 = refl

onePositiveAxisPoint : Geometry.Ternary27Point
onePositiveAxisPoint = Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero

onePositiveAxisPointHasS2 :
  voxelStabiliser onePositiveAxisPoint ≡ Symmetry.pairStabiliserS2
onePositiveAxisPointHasS2 = refl

threeDistinctPoint : Geometry.Ternary27Point
threeDistinctPoint = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne

threeDistinctPointHasTrivialStabiliser :
  voxelStabiliser threeDistinctPoint ≡ Symmetry.trivialStabiliser
threeDistinctPointHasTrivialStabiliser = refl

------------------------------------------------------------------------
-- 2. Coordinate permutation generators on the 27-cube.
------------------------------------------------------------------------

swapXY : Geometry.Ternary27Point → Geometry.Ternary27Point
swapXY (Geometry.ternary27Point x y z) = Geometry.ternary27Point y x z

rotateXYZ : Geometry.Ternary27Point → Geometry.Ternary27Point
rotateXYZ (Geometry.ternary27Point x y z) = Geometry.ternary27Point y z x

swapXYInvolutive : (p : Geometry.Ternary27Point) → swapXY (swapXY p) ≡ p
swapXYInvolutive (Geometry.ternary27Point x y z) = refl

rotateXYZOrderThree :
  (p : Geometry.Ternary27Point) → rotateXYZ (rotateXYZ (rotateXYZ p)) ≡ p
rotateXYZOrderThree (Geometry.ternary27Point x y z) = refl

originFixedBySwap : swapXY Geometry.origin ≡ Geometry.origin
originFixedBySwap = refl

originFixedByRotation : rotateXYZ Geometry.origin ≡ Geometry.origin
originFixedByRotation = refl

positiveCornerFixedBySwap : swapXY Geometry.positiveCorner ≡ Geometry.positiveCorner
positiveCornerFixedBySwap = refl

positiveCornerFixedByRotation : rotateXYZ Geometry.positiveCorner ≡ Geometry.positiveCorner
positiveCornerFixedByRotation = refl

------------------------------------------------------------------------
-- 3. Depth-one C3 Fourier sectors on one ternary axis.
------------------------------------------------------------------------

data AxisFrequency : Set where
  frequencyZero frequencyPositive frequencyNegative : AxisFrequency

frequencyRow : AxisFrequency → Fourier.FourierRow
frequencyRow frequencyZero = Fourier.chi0
frequencyRow frequencyPositive = Fourier.chi1
frequencyRow frequencyNegative = Fourier.chi2

conjugateFrequency : AxisFrequency → AxisFrequency
conjugateFrequency frequencyZero = frequencyZero
conjugateFrequency frequencyPositive = frequencyNegative
conjugateFrequency frequencyNegative = frequencyPositive

conjugateFrequencyInvolutive :
  (f : AxisFrequency) → conjugateFrequency (conjugateFrequency f) ≡ f
conjugateFrequencyInvolutive frequencyZero = refl
conjugateFrequencyInvolutive frequencyPositive = refl
conjugateFrequencyInvolutive frequencyNegative = refl

conjugateFrequencyRowExact :
  (f : AxisFrequency) →
  Fourier.conjugateRow (frequencyRow f) ≡ frequencyRow (conjugateFrequency f)
conjugateFrequencyRowExact frequencyZero = Fourier.chi0IsFixedByConjugation
conjugateFrequencyRowExact frequencyPositive = Fourier.chi1ConjugateIsChi2
conjugateFrequencyRowExact frequencyNegative = Fourier.chi2ConjugateIsChi1

------------------------------------------------------------------------
-- 4. Tensor-labelled C3^3 sectors for a single 27-point cube.
--
-- This is a sector index product, not yet a supplied 27-point transform.
------------------------------------------------------------------------

record CubeFrequencySector : Set where
  constructor cubeFrequencySector
  field
    fx fy fz : AxisFrequency

open CubeFrequencySector public

cubeSectorCount : Nat
cubeSectorCount = 3 * 3 * 3

cubeSectorCountIs27 : cubeSectorCount ≡ 27
cubeSectorCountIs27 = refl

trivialCubeSector : CubeFrequencySector
trivialCubeSector = cubeFrequencySector frequencyZero frequencyZero frequencyZero

conjugateCubeSector : CubeFrequencySector → CubeFrequencySector
conjugateCubeSector (cubeFrequencySector a b c) =
  cubeFrequencySector
    (conjugateFrequency a)
    (conjugateFrequency b)
    (conjugateFrequency c)

cubeSectorConjugationInvolutive :
  (s : CubeFrequencySector) → conjugateCubeSector (conjugateCubeSector s) ≡ s
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyZero frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyZero frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyZero frequencyNegative) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyPositive frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyPositive frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyPositive frequencyNegative) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyNegative frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyNegative frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyZero frequencyNegative frequencyNegative) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyZero frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyZero frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyZero frequencyNegative) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyPositive frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyPositive frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyPositive frequencyNegative) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyNegative frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyNegative frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyPositive frequencyNegative frequencyNegative) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyZero frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyZero frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyZero frequencyNegative) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyPositive frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyPositive frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyPositive frequencyNegative) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyNegative frequencyZero) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyNegative frequencyPositive) = refl
cubeSectorConjugationInvolutive (cubeFrequencySector frequencyNegative frequencyNegative frequencyNegative) = refl

swapSectorXY : CubeFrequencySector → CubeFrequencySector
swapSectorXY (cubeFrequencySector a b c) = cubeFrequencySector b a c

rotateSectorXYZ : CubeFrequencySector → CubeFrequencySector
rotateSectorXYZ (cubeFrequencySector a b c) = cubeFrequencySector b c a

swapSectorXYInvolutive : (s : CubeFrequencySector) → swapSectorXY (swapSectorXY s) ≡ s
swapSectorXYInvolutive (cubeFrequencySector a b c) = refl

rotateSectorXYZOrderThree :
  (s : CubeFrequencySector) →
  rotateSectorXYZ (rotateSectorXYZ (rotateSectorXYZ s)) ≡ s
rotateSectorXYZOrderThree (cubeFrequencySector a b c) = refl

------------------------------------------------------------------------
-- 5. Three 27-sector cubes give a 27^3 = 19683 sector-labelled hyperfabric.
------------------------------------------------------------------------

record HyperformalFrequencySector : Set where
  constructor hyperformalFrequencySector
  field
    interactionSector : CubeFrequencySector
    appraisalASector : CubeFrequencySector
    appraisalBSector : CubeFrequencySector

open HyperformalFrequencySector public

hyperfabricSectorCount : Nat
hyperfabricSectorCount = 27 * 27 * 27

hyperfabricSectorCountIs19683 : hyperfabricSectorCount ≡ 19683
hyperfabricSectorCountIs19683 = refl

conjugateHyperformalSector : HyperformalFrequencySector → HyperformalFrequencySector
conjugateHyperformalSector
  (hyperformalFrequencySector i a b) =
  hyperformalFrequencySector
    (conjugateCubeSector i)
    (conjugateCubeSector a)
    (conjugateCubeSector b)

------------------------------------------------------------------------
-- 6. Existing spectral/irrep interfaces are pinned without supplying a fake
--    kernel or claiming an unsupplied transform.
------------------------------------------------------------------------

axisCharacterFamilyIsExact : Bool
axisCharacterFamilyIsExact = true

cubeCharacterProductSectorIndexed : Bool
cubeCharacterProductSectorIndexed = true

DepthOneSpectralCodecInterface : Set₁
DepthOneSpectralCodecInterface = Irrep.ExactSpectralCodec 1

DepthOneCharacterTransformInterface : Set₁
DepthOneCharacterTransformInterface = Irrep.FiniteCharacterTransform 1

fullCubeDFTConstructedHere : Bool
fullCubeDFTConstructedHere = false

parsevalEstablishedHere : Bool
parsevalEstablishedHere = false

schurDiagonalisationEstablishedHere : Bool
schurDiagonalisationEstablishedHere = false

------------------------------------------------------------------------
-- 7. Monster/Ogg seam: projection/intertwining only.
------------------------------------------------------------------------

monsterP3CommonTrit : SSP.SSPTrit
monsterP3CommonTrit = Carrier.monsterOggToCommonTrit Lane.p3

monsterP3MapsToNeutral : monsterP3CommonTrit ≡ SSP.sspZero
monsterP3MapsToNeutral = Carrier.monsterThreeMapsToCommonNeutral

monsterP3AxisAnchor : Geometry.Ternary27Point
monsterP3AxisAnchor =
  Geometry.ternary27Point monsterP3CommonTrit SSP.sspZero SSP.sspZero

monsterP3AxisAnchorIsOrigin : monsterP3AxisAnchor ≡ Geometry.origin
monsterP3AxisAnchorIsOrigin rewrite monsterP3MapsToNeutral = refl

monsterConjugationIntertwinerAvailable : Bool
monsterConjugationIntertwinerAvailable = true

------------------------------------------------------------------------
-- 8. Exact claim boundary.
------------------------------------------------------------------------

record Base369Ternary27SpectralSymmetryBoundary : Set where
  constructor base369Ternary27SpectralSymmetryBoundary
  field
    voxelCarriesCoordinatePermutationSymmetry : Bool
    voxelStabiliserClassifiedByExistingS3Owner : Bool
    depthOneC3CharactersExactOnEachAxis : Bool
    cubeHasTwentySevenTensorFrequencyLabels : Bool
    hyperfabricHasNineteenThousandSixHundredEightyThreeTensorLabels : Bool
    frequencyConjugationExact : Bool
    monster3BConjugationIntertwinerReused : Bool
    monsterOggProjectionCreatesRepresentationEquivalence : Bool
    fullTwentySevenPointDFTConstructed : Bool
    parsevalIdentityEstablished : Bool
    schurDiagonalisationEstablished : Bool
    hypervoxelIsMonsterRepresentation : Bool

canonicalBase369Ternary27SpectralSymmetryBoundary :
  Base369Ternary27SpectralSymmetryBoundary
canonicalBase369Ternary27SpectralSymmetryBoundary =
  base369Ternary27SpectralSymmetryBoundary
    true true true true true true true false false false false false
