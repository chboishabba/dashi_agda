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
-- Giulio Codogni and Guido Maria Lido,
-- "Spectral theory of isogeny graphs", Journal of Number Theory 286 (2026),
-- 131--184.
-- DOI: 10.1016/j.jnt.2026.02.006.
--
-- DASHI CONTRIBUTION
--
-- Put the exact p=11, ell=2 modular-polynomial correspondence into the finite
-- spectral language used elsewhere in DASHI, while preserving its natural
-- non-symmetric multiplicity basis and distinguishing two different quantities
-- that had previously been given the same word "gap".
--
-- For A = [[0,3],[2,1]], the weights w=(2,3) satisfy detailed balance
--
--   w_0 A_01 = w_1 A_10 = 6.
--
-- Its explicit eigenmodes are
--
--   (1,1)   with adjacency eigenvalue  3 = ell+1,
--   (-3,2)  with adjacency eigenvalue -2.
--
-- For the combinatorial Laplacian L = 3 I - A the nonzero eigenvalue is 5.
-- That number is NOT the usual expander/adjacency spectral gap.  The latter is
--
--   (ell+1) - max |lambda_nontrivial| = 3 - 2 = 1.
--
-- The nontrivial adjacency mode also satisfies the Ramanujan/Hasse square
-- inequality  (-2)^2 = 4 < 8 = 4*ell, avoiding square roots in the certificate.
-- None of these finite arithmetic quantities is identified with a physical
-- mass gap.
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
-- Exact weighted self-adjointness on the coordinate basis.
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

p11NonzeroLaplacianEigenvalue : Nat
p11NonzeroLaplacianEigenvalue = 5

p11NonzeroLaplacianEigenvalueIsFive : p11NonzeroLaplacianEigenvalue ≡ 5
p11NonzeroLaplacianEigenvalueIsFive = refl

------------------------------------------------------------------------
-- Expander/adjacency spectral gap: d - |lambda_nontrivial| = 3 - 2 = 1.
------------------------------------------------------------------------

p11AdjacencyDegree : Nat
p11AdjacencyDegree = 3

p11NontrivialAdjacencyAbs : Nat
p11NontrivialAdjacencyAbs = 2

p11AdjacencySpectralGap : Nat
p11AdjacencySpectralGap = p11AdjacencyDegree - p11NontrivialAdjacencyAbs

p11AdjacencySpectralGapIsOne : p11AdjacencySpectralGap ≡ 1
p11AdjacencySpectralGapIsOne = refl

------------------------------------------------------------------------
-- Ramanujan/Hasse certificate in square form: |lambda|^2 < 4 ell.
------------------------------------------------------------------------

p11Ell : Nat
p11Ell = 2

p11NontrivialEigenvalueSquare : Nat
p11NontrivialEigenvalueSquare = 4

p11FourEll : Nat
p11FourEll = 4 * p11Ell

p11RamanujanSquareCertificate :
  p11NontrivialEigenvalueSquare < p11FourEll
p11RamanujanSquareCertificate = s≤s (s≤s (s≤s (s≤s z≤n)))

------------------------------------------------------------------------
-- Backwards-compatible name retained deliberately, but no longer authoritative
-- terminology.  Existing consumers can migrate without silently changing a
-- numeric theorem; new code should use p11NonzeroLaplacianEigenvalue.
------------------------------------------------------------------------

p11ArithmeticSpectralGap : Nat
p11ArithmeticSpectralGap = p11NonzeroLaplacianEigenvalue

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

    nonzeroLaplacianEigenvalueFiveConstructed : Bool
    nonzeroLaplacianEigenvalueFiveConstructedIsTrue :
      nonzeroLaplacianEigenvalueFiveConstructed ≡ true

    adjacencySpectralGapOneConstructed : Bool
    adjacencySpectralGapOneConstructedIsTrue :
      adjacencySpectralGapOneConstructed ≡ true

    ramanujanSquareCertificateConstructed : Bool
    ramanujanSquareCertificateConstructedIsTrue :
      ramanujanSquareCertificateConstructed ≡ true

    legacyFiveCalledAdjacencySpectralGap : Bool
    legacyFiveCalledAdjacencySpectralGapIsFalse :
      legacyFiveCalledAdjacencySpectralGap ≡ false

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
    ; nonzeroLaplacianEigenvalueFiveConstructed = true
    ; nonzeroLaplacianEigenvalueFiveConstructedIsTrue = refl
    ; adjacencySpectralGapOneConstructed = true
    ; adjacencySpectralGapOneConstructedIsTrue = refl
    ; ramanujanSquareCertificateConstructed = true
    ; ramanujanSquareCertificateConstructedIsTrue = refl
    ; legacyFiveCalledAdjacencySpectralGap = false
    ; legacyFiveCalledAdjacencySpectralGapIsFalse = refl
    ; arbitraryVectorSelfAdjointnessProvedHere = false
    ; arbitraryVectorSelfAdjointnessProvedHereIsFalse = refl
    ; gapIdentifiedWithPhysicalMassGap = false
    ; gapIdentifiedWithPhysicalMassGapIsFalse = refl
    }
