module DASHI.Moonshine.P11BrandtPrimeGeneratorsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapters 41--42 identify Brandt operators with Hecke operators on the
-- definite-quaternion / supersingular module.
--
-- Giulio Codogni and Guido Maria Lido,
-- "Spectral theory of isogeny graphs", Journal of Number Theory 286 (2026),
-- 131--184.
-- DOI: 10.1016/j.jnt.2026.02.006.
-- Nontrivial supersingular-isogeny adjacency eigenvalues satisfy the
-- Ramanujan/Hasse bound |lambda| < 2 sqrt(ell) in the connected setting.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
-- Provides the Hecke/newform framework used to identify the nontrivial Brandt
-- eigenline with the weight-2 level-11 cusp form.
--
-- SOURCE DATA / FINITE COEFFICIENT CHECK
--
-- The unique normalized weight-2 level-11 newform is
--
--   eta(z)^2 eta(11z)^2
--     = q - 2 q^2 - q^3 + 2 q^4 + q^5 + ... .
--
-- Thus a_2=-2, a_3=-1, a_5=1.  This q-expansion is also recorded by the
-- American Institute of Mathematics L-function/newform tables and LMFDB.
-- No DOI is asserted for those datasets themselves.
--
-- DASHI CONTRIBUTION
--
-- On the now source-certified p=11 two-class supersingular carrier, combine:
--
--   * row degree ell+1,
--   * automorphism-weight detailed balance 2*b_01 = 3*b_10,
--   * nontrivial Brandt eigenvalue a_ell,
--
-- to construct the first three prime Brandt generators:
--
--   B_11(2) = [[0,3],[2,1]],    eigenvalues 3,-2,
--   B_11(3) = [[1,3],[2,2]],    eigenvalues 4,-1,
--   B_11(5) = [[3,3],[2,4]],    eigenvalues 6, 1.
--
-- The ell=2 matrix is the independently constructed Phi_2 correspondence.
-- The ell=3 and ell=5 matrices are source-forced Brandt matrices from the
-- one-dimensional newform spectrum plus the geometric automorphism weights;
-- they are not presented as independent modular-polynomial reductions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11BrandtAutomorphismWeightExact as Weight

------------------------------------------------------------------------
-- Tiny two-state integer-matrix carrier.
------------------------------------------------------------------------

record P11BrandtMatrix : Set where
  constructor brandtMatrix
  field
    b00 b01 b10 b11 : Nat

open P11BrandtMatrix public

matrixAction : P11BrandtMatrix → P11.IntPair → P11.IntPair
matrixAction B v =
  P11.intPair
    (((+ (b00 B)) *ℤ P11.left v) +ℤ ((+ (b01 B)) *ℤ P11.right v))
    (((+ (b10 B)) *ℤ P11.left v) +ℤ ((+ (b11 B)) *ℤ P11.right v))

row0Degree : P11BrandtMatrix → Nat
row0Degree B = b00 B + b01 B

row1Degree : P11BrandtMatrix → Nat
row1Degree B = b10 B + b11 B

balanced : P11BrandtMatrix → Set
balanced B = 2 * b01 B ≡ 3 * b10 B

------------------------------------------------------------------------
-- The three prime generators.
------------------------------------------------------------------------

B11_2 : P11BrandtMatrix
B11_2 = brandtMatrix 0 3 2 1

B11_3 : P11BrandtMatrix
B11_3 = brandtMatrix 1 3 2 2

B11_5 : P11BrandtMatrix
B11_5 = brandtMatrix 3 3 2 4

B11_2MatchesPhi2 :
  b00 B11_2 ≡ P11.multiplicity P11.j0 P11.j0
  × b01 B11_2 ≡ P11.multiplicity P11.j0 P11.j1
  × b10 B11_2 ≡ P11.multiplicity P11.j1 P11.j0
  × b11 B11_2 ≡ P11.multiplicity P11.j1 P11.j1
B11_2MatchesPhi2 = refl , refl , refl , refl

B11_2RowsHaveDegree3 : row0Degree B11_2 ≡ 3 × row1Degree B11_2 ≡ 3
B11_2RowsHaveDegree3 = refl , refl

B11_3RowsHaveDegree4 : row0Degree B11_3 ≡ 4 × row1Degree B11_3 ≡ 4
B11_3RowsHaveDegree4 = refl , refl

B11_5RowsHaveDegree6 : row0Degree B11_5 ≡ 6 × row1Degree B11_5 ≡ 6
B11_5RowsHaveDegree6 = refl , refl

B11_2Balanced : balanced B11_2
B11_2Balanced = refl

B11_3Balanced : balanced B11_3
B11_3Balanced = refl

B11_5Balanced : balanced B11_5
B11_5Balanced = refl

------------------------------------------------------------------------
-- Common eigenbasis: constant mode and the automorphism-orthogonal mode.
------------------------------------------------------------------------

B11_2Constant :
  matrixAction B11_2 P11.constantEigenvector
  ≡ P11.scalePair (+ 3) P11.constantEigenvector
B11_2Constant = refl

B11_2Nonconstant :
  matrixAction B11_2 P11.nonconstantEigenvector
  ≡ P11.scalePair (-[1+ 1 ]) P11.nonconstantEigenvector
B11_2Nonconstant = refl

B11_3Constant :
  matrixAction B11_3 P11.constantEigenvector
  ≡ P11.scalePair (+ 4) P11.constantEigenvector
B11_3Constant = refl

B11_3Nonconstant :
  matrixAction B11_3 P11.nonconstantEigenvector
  ≡ P11.scalePair (-[1+ 0 ]) P11.nonconstantEigenvector
B11_3Nonconstant = refl

B11_5Constant :
  matrixAction B11_5 P11.constantEigenvector
  ≡ P11.scalePair (+ 6) P11.constantEigenvector
B11_5Constant = refl

B11_5Nonconstant :
  matrixAction B11_5 P11.nonconstantEigenvector
  ≡ P11.scalePair (+ 1) P11.nonconstantEigenvector
B11_5Nonconstant = refl

------------------------------------------------------------------------
-- Source q-expansion coefficients on the nontrivial line.
------------------------------------------------------------------------

level11a2 level11a3 level11a5 : ℤ
level11a2 = -[1+ 1 ]
level11a3 = -[1+ 0 ]
level11a5 = + 1

B11_2NonconstantMatchesNewform :
  matrixAction B11_2 P11.nonconstantEigenvector
  ≡ P11.scalePair level11a2 P11.nonconstantEigenvector
B11_2NonconstantMatchesNewform = refl

B11_3NonconstantMatchesNewform :
  matrixAction B11_3 P11.nonconstantEigenvector
  ≡ P11.scalePair level11a3 P11.nonconstantEigenvector
B11_3NonconstantMatchesNewform = refl

B11_5NonconstantMatchesNewform :
  matrixAction B11_5 P11.nonconstantEigenvector
  ≡ P11.scalePair level11a5 P11.nonconstantEigenvector
B11_5NonconstantMatchesNewform = refl

------------------------------------------------------------------------
-- Ramanujan certificates using integer squares, avoiding sqrt.
------------------------------------------------------------------------

ell2RamanujanSquare : 4 < 4 * 2
ell2RamanujanSquare = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

ell3RamanujanSquare : 1 < 4 * 3
ell3RamanujanSquare = s≤s (s≤s z≤n)

ell5RamanujanSquare : 1 < 4 * 5
ell5RamanujanSquare = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- The automorphism-derived geometric balance is the same one used by every
-- generator in this first fixed-characteristic family.
------------------------------------------------------------------------

ell2BalanceUsesGeometricWeights :
  2 * b01 B11_2 ≡ 3 * b10 B11_2
ell2BalanceUsesGeometricWeights = Weight.geometricDetailedBalanceEll2

record P11BrandtPrimeGeneratorBoundary : Set where
  field
    ell2IndependentPhi2GeneratorConstructed : Bool
    ell2IndependentPhi2GeneratorConstructedIsTrue :
      ell2IndependentPhi2GeneratorConstructed ≡ true

    ell3SourceForcedBrandtGeneratorConstructed : Bool
    ell3SourceForcedBrandtGeneratorConstructedIsTrue :
      ell3SourceForcedBrandtGeneratorConstructed ≡ true

    ell5SourceForcedBrandtGeneratorConstructed : Bool
    ell5SourceForcedBrandtGeneratorConstructedIsTrue :
      ell5SourceForcedBrandtGeneratorConstructed ≡ true

    allThreeUseAutomorphismBalance : Bool
    allThreeUseAutomorphismBalanceIsTrue : allThreeUseAutomorphismBalance ≡ true

    allThreeRamanujanSquaresCertified : Bool
    allThreeRamanujanSquaresCertifiedIsTrue :
      allThreeRamanujanSquaresCertified ≡ true

    ell3Ell5IndependentlyReducedFromModularPolynomialsHere : Bool
    ell3Ell5IndependentlyReducedFromModularPolynomialsHereIsFalse :
      ell3Ell5IndependentlyReducedFromModularPolynomialsHere ≡ false

canonicalP11BrandtPrimeGeneratorBoundary : P11BrandtPrimeGeneratorBoundary
canonicalP11BrandtPrimeGeneratorBoundary =
  record
    { ell2IndependentPhi2GeneratorConstructed = true
    ; ell2IndependentPhi2GeneratorConstructedIsTrue = refl
    ; ell3SourceForcedBrandtGeneratorConstructed = true
    ; ell3SourceForcedBrandtGeneratorConstructedIsTrue = refl
    ; ell5SourceForcedBrandtGeneratorConstructed = true
    ; ell5SourceForcedBrandtGeneratorConstructedIsTrue = refl
    ; allThreeUseAutomorphismBalance = true
    ; allThreeUseAutomorphismBalanceIsTrue = refl
    ; allThreeRamanujanSquaresCertified = true
    ; allThreeRamanujanSquaresCertifiedIsTrue = refl
    ; ell3Ell5IndependentlyReducedFromModularPolynomialsHere = false
    ; ell3Ell5IndependentlyReducedFromModularPolynomialsHereIsFalse = refl
    }
