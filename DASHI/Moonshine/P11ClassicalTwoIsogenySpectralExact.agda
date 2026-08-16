module DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Reinier Bröker, Kristin Lauter and Andrew V. Sutherland,
-- "Modular polynomials via isogeny volcanoes",
-- Mathematics of Computation 81 (2012), 1201--1231.
-- DOI: 10.1090/S0025-5718-2011-02508-1.
--
-- Fan R. K. Chung,
-- "Spectral Graph Theory", CBMS Regional Conference Series in Mathematics 92,
-- American Mathematical Society, 1997.
-- DOI: 10.1090/cbms/092.
--
-- DASHI CONTRIBUTION
--
-- Put the exact p=11, ell=2 modular-polynomial correspondence into the same
-- finite spectral language used elsewhere in DASHI, while preserving its
-- natural non-symmetric multiplicity basis.
--
-- For A = [[0,3],[2,1]], the weights w=(2,3) satisfy detailed balance
--
--   w_0 A_01 = w_1 A_10 = 6.
--
-- The four basis pairings therefore satisfy weighted self-adjointness exactly.
-- Its explicit eigenmodes are
--
--   (1,1)   with lambda = 3,
--   (-3,2)  with lambda = -2,
--
-- and these modes are weighted-orthogonal.  The degree-three Laplacian
--
--   L = 3 I - A
--
-- has eigenvalues 0 and 5 on those two independent modes.  This is an exact
-- finite arithmetic gap, not an imported physical mass-gap claim.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _-ℤ_)

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11

weightJ0 weightJ1 : ℤ
weightJ0 = + 2
weightJ1 = + 3

detailedBalanceOffDiagonal :
  weightJ0 *ℤ (+ 3) ≡ weightJ1 *ℤ (+ 2)
detailedBalanceOffDiagonal = refl

weightedPairing : P11.IntPair → P11.IntPair → ℤ
weightedPairing u v =
  (weightJ0 *ℤ (P11.left u *ℤ P11.left v))
  +ℤ
  (weightJ1 *ℤ (P11.right u *ℤ P11.right v))

constantAndNonconstantOrthogonal :
  weightedPairing P11.constantEigenvector P11.nonconstantEigenvector ≡ + 0
constantAndNonconstantOrthogonal = refl

------------------------------------------------------------------------
-- Exact weighted self-adjointness on the coordinate basis.  This is the finite
-- matrix content needed here; no general integer-bilinearity theorem is hidden
-- behind refl.
------------------------------------------------------------------------

basisJ0 basisJ1 : P11.IntPair
basisJ0 = P11.intPair (+ 1) (+ 0)
basisJ1 = P11.intPair (+ 0) (+ 1)

weightedSelfAdjoint00 :
  weightedPairing (P11.matrixAction basisJ0) basisJ0
  ≡ weightedPairing basisJ0 (P11.matrixAction basisJ0)
weightedSelfAdjoint00 = refl

weightedSelfAdjoint01 :
  weightedPairing (P11.matrixAction basisJ0) basisJ1
  ≡ weightedPairing basisJ0 (P11.matrixAction basisJ1)
weightedSelfAdjoint01 = refl

weightedSelfAdjoint10 :
  weightedPairing (P11.matrixAction basisJ1) basisJ0
  ≡ weightedPairing basisJ1 (P11.matrixAction basisJ0)
weightedSelfAdjoint10 = refl

weightedSelfAdjoint11 :
  weightedPairing (P11.matrixAction basisJ1) basisJ1
  ≡ weightedPairing basisJ1 (P11.matrixAction basisJ1)
weightedSelfAdjoint11 = refl

------------------------------------------------------------------------
-- Degree-three Laplacian L = 3I - A.
------------------------------------------------------------------------

laplacian : P11.IntPair → P11.IntPair
laplacian vector =
  P11.intPair
    (((+ 3) *ℤ P11.left vector) -ℤ P11.left (P11.matrixAction vector))
    (((+ 3) *ℤ P11.right vector) -ℤ P11.right (P11.matrixAction vector))

constantLaplacianModeIsZero :
  laplacian P11.constantEigenvector ≡ P11.scalePair (+ 0) P11.constantEigenvector
constantLaplacianModeIsZero = refl

nonconstantLaplacianModeIsFive :
  laplacian P11.nonconstantEigenvector ≡ P11.scalePair (+ 5) P11.nonconstantEigenvector
nonconstantLaplacianModeIsFive = refl

p11ArithmeticSpectralGap : Nat
p11ArithmeticSpectralGap = 5

p11ArithmeticSpectralGapIsFive : p11ArithmeticSpectralGap ≡ 5
p11ArithmeticSpectralGapIsFive = refl

record P11ArithmeticSpectralBoundary : Set where
  field
    detailedBalanceConstructed : Bool
    detailedBalanceConstructedIsTrue : detailedBalanceConstructed ≡ true

    basisWeightedSelfAdjointnessConstructed : Bool
    basisWeightedSelfAdjointnessConstructedIsTrue :
      basisWeightedSelfAdjointnessConstructed ≡ true

    weightedOrthogonalModesConstructed : Bool
    weightedOrthogonalModesConstructedIsTrue :
      weightedOrthogonalModesConstructed ≡ true

    exactFiniteGapConstructed : Bool
    exactFiniteGapConstructedIsTrue : exactFiniteGapConstructed ≡ true

    arbitraryVectorSelfAdjointnessProvedHere : Bool
    arbitraryVectorSelfAdjointnessProvedHereIsFalse :
      arbitraryVectorSelfAdjointnessProvedHere ≡ false

    gapIdentifiedWithPhysicalMassGap : Bool
    gapIdentifiedWithPhysicalMassGapIsFalse :
      gapIdentifiedWithPhysicalMassGap ≡ false

canonicalP11ArithmeticSpectralBoundary : P11ArithmeticSpectralBoundary
canonicalP11ArithmeticSpectralBoundary =
  record
    { detailedBalanceConstructed = true
    ; detailedBalanceConstructedIsTrue = refl
    ; basisWeightedSelfAdjointnessConstructed = true
    ; basisWeightedSelfAdjointnessConstructedIsTrue = refl
    ; weightedOrthogonalModesConstructed = true
    ; weightedOrthogonalModesConstructedIsTrue = refl
    ; exactFiniteGapConstructed = true
    ; exactFiniteGapConstructedIsTrue = refl
    ; arbitraryVectorSelfAdjointnessProvedHere = false
    ; arbitraryVectorSelfAdjointnessProvedHereIsFalse = refl
    ; gapIdentifiedWithPhysicalMassGap = false
    ; gapIdentifiedWithPhysicalMassGapIsFalse = refl
    }
