module DASHI.Moonshine.Base369Ternary27PathCubeSpectralBandsExact where

------------------------------------------------------------------------
-- ACTUAL NON-PERIODIC 3x3x3 GRID SPECTRAL BAND COMBINATORICS
--
-- The hypervoxel adjacency defined in the geometry owner is P3 □ P3 □ P3:
-- -1 <-> 0 <-> +1 on each axis, with NO wraparound edge -1 <-> +1.
-- Therefore it is not the Cayley graph of C3^3.  C3^3 characters remain exact
-- character labels for the product cyclic carrier, but are not automatically
-- adjacency/Laplacian eigenvectors of this non-periodic grid.
--
-- For the path P3, the three adjacency eigenvalue TYPES are
--   -sqrt(2), 0, +sqrt(2).
-- For the Cartesian cube, tensor sums give seven coefficient bands
--   k*sqrt(2), k=-3..3,
-- with multiplicities 1,3,6,7,6,3,1.
-- This module records that exact finite combinatorics without constructing
-- real-number eigenvectors or claiming a kernel-checked diagonalisation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Moonshine.Base369Ternary27CharacterAdjacencyEquivarianceExact as Character

------------------------------------------------------------------------
-- 1. One-axis path modes.
------------------------------------------------------------------------

data Path3SpectralMode : Set where
  negativePathMode zeroPathMode positivePathMode : Path3SpectralMode

------------------------------------------------------------------------
-- 2. Seven tensor-sum bands for P3 □ P3 □ P3.
------------------------------------------------------------------------

data CubeSpectralBand : Set where
  bandMinus3 bandMinus2 bandMinus1 bandZero bandPlus1 bandPlus2 bandPlus3
    : CubeSpectralBand

bandMultiplicity : CubeSpectralBand → Nat
bandMultiplicity bandMinus3 = 1
bandMultiplicity bandMinus2 = 3
bandMultiplicity bandMinus1 = 6
bandMultiplicity bandZero = 7
bandMultiplicity bandPlus1 = 6
bandMultiplicity bandPlus2 = 3
bandMultiplicity bandPlus3 = 1

spectralMultiplicityTotal : Nat
spectralMultiplicityTotal =
  bandMultiplicity bandMinus3
  + bandMultiplicity bandMinus2
  + bandMultiplicity bandMinus1
  + bandMultiplicity bandZero
  + bandMultiplicity bandPlus1
  + bandMultiplicity bandPlus2
  + bandMultiplicity bandPlus3

spectralMultiplicityTotalIs27 : spectralMultiplicityTotal ≡ 27
spectralMultiplicityTotalIs27 = refl

------------------------------------------------------------------------
-- 3. Band reflection symmetry.
------------------------------------------------------------------------

reflectBand : CubeSpectralBand → CubeSpectralBand
reflectBand bandMinus3 = bandPlus3
reflectBand bandMinus2 = bandPlus2
reflectBand bandMinus1 = bandPlus1
reflectBand bandZero = bandZero
reflectBand bandPlus1 = bandMinus1
reflectBand bandPlus2 = bandMinus2
reflectBand bandPlus3 = bandMinus3

reflectBandInvolutive : (b : CubeSpectralBand) → reflectBand (reflectBand b) ≡ b
reflectBandInvolutive bandMinus3 = refl
reflectBandInvolutive bandMinus2 = refl
reflectBandInvolutive bandMinus1 = refl
reflectBandInvolutive bandZero = refl
reflectBandInvolutive bandPlus1 = refl
reflectBandInvolutive bandPlus2 = refl
reflectBandInvolutive bandPlus3 = refl

reflectionPreservesMultiplicity :
  (b : CubeSpectralBand) → bandMultiplicity (reflectBand b) ≡ bandMultiplicity b
reflectionPreservesMultiplicity bandMinus3 = refl
reflectionPreservesMultiplicity bandMinus2 = refl
reflectionPreservesMultiplicity bandMinus1 = refl
reflectionPreservesMultiplicity bandZero = refl
reflectionPreservesMultiplicity bandPlus1 = refl
reflectionPreservesMultiplicity bandPlus2 = refl
reflectionPreservesMultiplicity bandPlus3 = refl

------------------------------------------------------------------------
-- 4. Critical torus/box non-collapse.
------------------------------------------------------------------------

record PeriodicVsPathCubeSpectralBoundary : Set where
  constructor periodicVsPathCubeSpectralBoundary
  field
    voxelAdjacencyHasWraparound : Bool
    voxelGraphIsC3CubedCayleyGraph : Bool
    c3CubedCharactersAreExactCharacterLabels : Bool
    c3CubedCharactersAutomaticallyDiagonalisePathCubeAdjacency : Bool
    pathCubeHasSevenTensorSumBands : Bool
    sevenBandMultiplicitiesSumToTwentySeven : Bool
    realEigenvectorsConstructedHere : Bool
    exactSqrtTwoScalarModelConstructedHere : Bool

canonicalPeriodicVsPathCubeSpectralBoundary : PeriodicVsPathCubeSpectralBoundary
canonicalPeriodicVsPathCubeSpectralBoundary =
  periodicVsPathCubeSpectralBoundary
    false false true false true true false false

c3CharacterLabelsDoNotPromoteAdjacencyDiagonalisation :
  Character.Ternary27CharacterAdjacencyBoundary.graphLaplacianDiagonalisedHere
    Character.canonicalTernary27CharacterAdjacencyBoundary ≡ false
c3CharacterLabelsDoNotPromoteAdjacencyDiagonalisation = refl
