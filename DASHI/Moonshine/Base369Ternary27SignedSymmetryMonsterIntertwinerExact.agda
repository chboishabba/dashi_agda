module DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact where

------------------------------------------------------------------------
-- SIGNED-PERMUTATION SYMMETRY OF THE 3x3x3 TERNARY VOXEL
--
-- Spatial sign reversal on one ternary coordinate is an actual automorphism
-- of the nearest-neighbour grid.  On C3 characters the same reversal sends
-- k to -k, hence exchanges the two nontrivial Fourier sectors.  This is the
-- exact geometric seam to the existing Monster 3B phase-inversion transport.
--
-- No claim is made that the signed-permutation group embeds in the Monster or
-- that the voxel itself is a Monster module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.Monster3BPhaseTransportExact as Monster
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Bridge
import DASHI.Moonshine.Base369Ternary27CharacterAdjacencyEquivarianceExact as Character

negateTrit : SSP.SSPTrit → SSP.SSPTrit
negateTrit SSP.sspNegOne = SSP.sspPosOne
negateTrit SSP.sspZero = SSP.sspZero
negateTrit SSP.sspPosOne = SSP.sspNegOne

negateTritInvolutive : (t : SSP.SSPTrit) → negateTrit (negateTrit t) ≡ t
negateTritInvolutive SSP.sspNegOne = refl
negateTritInvolutive SSP.sspZero = refl
negateTritInvolutive SSP.sspPosOne = refl

negateGridStep :
  ∀ {a b} → Geometry.TritGridStep a b →
  Geometry.TritGridStep (negateTrit a) (negateTrit b)
negateGridStep Geometry.negToZero = Geometry.posToZero
negateGridStep Geometry.zeroToNeg = Geometry.zeroToPos
negateGridStep Geometry.zeroToPos = Geometry.zeroToNeg
negateGridStep Geometry.posToZero = Geometry.negToZero

flipX : Geometry.Ternary27Point → Geometry.Ternary27Point
flipX (Geometry.ternary27Point x y z) =
  Geometry.ternary27Point (negateTrit x) y z

flipY : Geometry.Ternary27Point → Geometry.Ternary27Point
flipY (Geometry.ternary27Point x y z) =
  Geometry.ternary27Point x (negateTrit y) z

flipZ : Geometry.Ternary27Point → Geometry.Ternary27Point
flipZ (Geometry.ternary27Point x y z) =
  Geometry.ternary27Point x y (negateTrit z)

flipXInvolutive : (p : Geometry.Ternary27Point) → flipX (flipX p) ≡ p
flipXInvolutive (Geometry.ternary27Point SSP.sspNegOne y z) = refl
flipXInvolutive (Geometry.ternary27Point SSP.sspZero y z) = refl
flipXInvolutive (Geometry.ternary27Point SSP.sspPosOne y z) = refl

flipYInvolutive : (p : Geometry.Ternary27Point) → flipY (flipY p) ≡ p
flipYInvolutive (Geometry.ternary27Point x SSP.sspNegOne z) = refl
flipYInvolutive (Geometry.ternary27Point x SSP.sspZero z) = refl
flipYInvolutive (Geometry.ternary27Point x SSP.sspPosOne z) = refl

flipZInvolutive : (p : Geometry.Ternary27Point) → flipZ (flipZ p) ≡ p
flipZInvolutive (Geometry.ternary27Point x y SSP.sspNegOne) = refl
flipZInvolutive (Geometry.ternary27Point x y SSP.sspZero) = refl
flipZInvolutive (Geometry.ternary27Point x y SSP.sspPosOne) = refl

originFixedByFlipX : flipX Geometry.origin ≡ Geometry.origin
originFixedByFlipX = refl
originFixedByFlipY : flipY Geometry.origin ≡ Geometry.origin
originFixedByFlipY = refl
originFixedByFlipZ : flipZ Geometry.origin ≡ Geometry.origin
originFixedByFlipZ = refl

flipXPreservesAdjacency :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q →
  Geometry.HypervoxelAdjacent (flipX p) (flipX q)
flipXPreservesAdjacency (Geometry.adjacentX step) = Geometry.adjacentX (negateGridStep step)
flipXPreservesAdjacency (Geometry.adjacentY step) = Geometry.adjacentY step
flipXPreservesAdjacency (Geometry.adjacentZ step) = Geometry.adjacentZ step

flipYPreservesAdjacency :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q →
  Geometry.HypervoxelAdjacent (flipY p) (flipY q)
flipYPreservesAdjacency (Geometry.adjacentX step) = Geometry.adjacentX step
flipYPreservesAdjacency (Geometry.adjacentY step) = Geometry.adjacentY (negateGridStep step)
flipYPreservesAdjacency (Geometry.adjacentZ step) = Geometry.adjacentZ step

flipZPreservesAdjacency :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q →
  Geometry.HypervoxelAdjacent (flipZ p) (flipZ q)
flipZPreservesAdjacency (Geometry.adjacentX step) = Geometry.adjacentX step
flipZPreservesAdjacency (Geometry.adjacentY step) = Geometry.adjacentY step
flipZPreservesAdjacency (Geometry.adjacentZ step) = Geometry.adjacentZ (negateGridStep step)

flipXFlipYCommute :
  (p : Geometry.Ternary27Point) → flipX (flipY p) ≡ flipY (flipX p)
flipXFlipYCommute (Geometry.ternary27Point x y z) = refl

flipXFlipZCommute :
  (p : Geometry.Ternary27Point) → flipX (flipZ p) ≡ flipZ (flipX p)
flipXFlipZCommute (Geometry.ternary27Point x y z) = refl

flipYFlipZCommute :
  (p : Geometry.Ternary27Point) → flipY (flipZ p) ≡ flipZ (flipY p)
flipYFlipZCommute (Geometry.ternary27Point x y z) = refl

swapConjugatesXFlipToYFlip :
  (p : Geometry.Ternary27Point) →
  Bridge.swapXY (flipX (Bridge.swapXY p)) ≡ flipY p
swapConjugatesXFlipToYFlip (Geometry.ternary27Point x y z) = refl

rotationConjugatesXFlipToYFlip :
  (p : Geometry.Ternary27Point) →
  Bridge.rotateXYZ (Bridge.rotateXYZ (flipX (Bridge.rotateXYZ p))) ≡ flipY p
rotationConjugatesXFlipToYFlip (Geometry.ternary27Point x y z) = refl

reflectFrequencyX : Bridge.CubeFrequencySector → Bridge.CubeFrequencySector
reflectFrequencyX (Bridge.cubeFrequencySector fx fy fz) =
  Bridge.cubeFrequencySector (Bridge.conjugateFrequency fx) fy fz

reflectFrequencyY : Bridge.CubeFrequencySector → Bridge.CubeFrequencySector
reflectFrequencyY (Bridge.cubeFrequencySector fx fy fz) =
  Bridge.cubeFrequencySector fx (Bridge.conjugateFrequency fy) fz

reflectFrequencyZ : Bridge.CubeFrequencySector → Bridge.CubeFrequencySector
reflectFrequencyZ (Bridge.cubeFrequencySector fx fy fz) =
  Bridge.cubeFrequencySector fx fy (Bridge.conjugateFrequency fz)

axisFlipCharacterCovariance :
  (f : Bridge.AxisFrequency) →
  (t : SSP.SSPTrit) →
  Character.axisCharacterValue (Bridge.conjugateFrequency f) (negateTrit t)
  ≡ Character.axisCharacterValue f t
axisFlipCharacterCovariance Bridge.frequencyZero SSP.sspNegOne = refl
axisFlipCharacterCovariance Bridge.frequencyZero SSP.sspZero = refl
axisFlipCharacterCovariance Bridge.frequencyZero SSP.sspPosOne = refl
axisFlipCharacterCovariance Bridge.frequencyPositive SSP.sspNegOne = refl
axisFlipCharacterCovariance Bridge.frequencyPositive SSP.sspZero = refl
axisFlipCharacterCovariance Bridge.frequencyPositive SSP.sspPosOne = refl
axisFlipCharacterCovariance Bridge.frequencyNegative SSP.sspNegOne = refl
axisFlipCharacterCovariance Bridge.frequencyNegative SSP.sspZero = refl
axisFlipCharacterCovariance Bridge.frequencyNegative SSP.sspPosOne = refl

monsterAxisReflectionIntertwines :
  (f : Bridge.AxisFrequency) →
  (t : SSP.SSPTrit) →
  Fourier.phaseToMonster
    (Character.axisCharacterValue (Bridge.conjugateFrequency f) t)
  ≡ Monster.transportPhase Monster.invertsGenerator
      (Fourier.phaseToMonster (Character.axisCharacterValue f t))
monsterAxisReflectionIntertwines = Character.monsterAxisConjugationIntertwines

record SignedTernaryVoxelSymmetryBoundary : Set where
  constructor signedTernaryVoxelSymmetryBoundary
  field
    eachAxisReflectionIsInvolution : Bool
    eachAxisReflectionPreservesAdjacency : Bool
    coordinateReflectionsCommute : Bool
    coordinatePermutationsConjugateReflections : Bool
    spatialReflectionInducesFrequencyConjugation : Bool
    monster3BPhaseInversionMatchesFrequencyConjugation : Bool
    fullSignedPermutationGroupConstructedAsGroupObject : Bool
    signedPermutationGroupEmbeddedInMonster : Bool
    voxelRepresentationOfMonsterEstablished : Bool

canonicalSignedTernaryVoxelSymmetryBoundary : SignedTernaryVoxelSymmetryBoundary
canonicalSignedTernaryVoxelSymmetryBoundary =
  signedTernaryVoxelSymmetryBoundary true true true true true true false false false
