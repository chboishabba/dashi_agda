module DASHI.Moonshine.P11BrandtJointHeckeAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Aristotle (Harmonic), editor of the user-supplied Lean HeckeGeneral source
-- and its prime-power recurrence formalized elsewhere in DASHI.
--
-- DASHI CONTRIBUTION
--
-- Assemble the first actual finite joint Hecke algebra on one fixed geometric
-- supersingular carrier.  The three prime Brandt generators B_11(2), B_11(3),
-- B_11(5) commute pairwise by exact matrix multiplication, and their coprime
-- products give explicit composite operators.
--
-- The ell=2 square is connected to PR #567's independently checked relation
--
--   B_11(2)^2 = T_4(full) + 2 I,
--
-- where T_4(full) = Phi_4(cyclic) + I.  Thus
--
--   B_11(2)^2 = Phi_4(cyclic) + 3 I.
--
-- This keeps the cyclic/full-Hecke distinction visible while demonstrating
-- that the actual arithmetic Brandt operator obeys the Aristotle/Miyake
-- prime-square relation on both basis vectors and both eigenmodes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact as Spectral
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Brandt
import DASHI.Moonshine.P11AristotleHeckeSquareCrossPollinationExact as Square
import DASHI.Moonshine.P11Phi4CyclicVsFullHeckeExact as Phi4

compose : Brandt.P11BrandtMatrix → Brandt.P11BrandtMatrix → Brandt.P11BrandtMatrix
compose A B =
  Brandt.brandtMatrix
    (Brandt.b00 A * Brandt.b00 B + Brandt.b01 A * Brandt.b10 B)
    (Brandt.b00 A * Brandt.b01 B + Brandt.b01 A * Brandt.b11 B)
    (Brandt.b10 A * Brandt.b00 B + Brandt.b11 A * Brandt.b10 B)
    (Brandt.b10 A * Brandt.b01 B + Brandt.b11 A * Brandt.b11 B)

identityMatrix : Brandt.P11BrandtMatrix
identityMatrix = Brandt.brandtMatrix 1 0 0 1

B11_6 : Brandt.P11BrandtMatrix
B11_6 = Brandt.brandtMatrix 6 6 4 8

B11_10 : Brandt.P11BrandtMatrix
B11_10 = Brandt.brandtMatrix 6 12 8 10

B11_15 : Brandt.P11BrandtMatrix
B11_15 = Brandt.brandtMatrix 9 15 10 14

B2B3IsB6 : compose Brandt.B11_2 Brandt.B11_3 ≡ B11_6
B2B3IsB6 = refl

B3B2IsB6 : compose Brandt.B11_3 Brandt.B11_2 ≡ B11_6
B3B2IsB6 = refl

B2B5IsB10 : compose Brandt.B11_2 Brandt.B11_5 ≡ B11_10
B2B5IsB10 = refl

B5B2IsB10 : compose Brandt.B11_5 Brandt.B11_2 ≡ B11_10
B5B2IsB10 = refl

B3B5IsB15 : compose Brandt.B11_3 Brandt.B11_5 ≡ B11_15
B3B5IsB15 = refl

B5B3IsB15 : compose Brandt.B11_5 Brandt.B11_3 ≡ B11_15
B5B3IsB15 = refl

B2B3Commute :
  compose Brandt.B11_2 Brandt.B11_3 ≡ compose Brandt.B11_3 Brandt.B11_2
B2B3Commute = refl

B2B5Commute :
  compose Brandt.B11_2 Brandt.B11_5 ≡ compose Brandt.B11_5 Brandt.B11_2
B2B5Commute = refl

B3B5Commute :
  compose Brandt.B11_3 Brandt.B11_5 ≡ compose Brandt.B11_5 Brandt.B11_3
B3B5Commute = refl

B6ConstantEigenvalueTwelve :
  Brandt.matrixAction B11_6 P11.constantEigenvector
  ≡ P11.scalePair (+ 12) P11.constantEigenvector
B6ConstantEigenvalueTwelve = refl

B6NonconstantEigenvalueTwo :
  Brandt.matrixAction B11_6 P11.nonconstantEigenvector
  ≡ P11.scalePair (+ 2) P11.nonconstantEigenvector
B6NonconstantEigenvalueTwo = refl

B10ConstantEigenvalueEighteen :
  Brandt.matrixAction B11_10 P11.constantEigenvector
  ≡ P11.scalePair (+ 18) P11.constantEigenvector
B10ConstantEigenvalueEighteen = refl

B10NonconstantEigenvalueMinusTwo :
  Brandt.matrixAction B11_10 P11.nonconstantEigenvector
  ≡ P11.scalePair (-[1+ 1 ]) P11.nonconstantEigenvector
B10NonconstantEigenvalueMinusTwo = refl

B15ConstantEigenvalueTwentyFour :
  Brandt.matrixAction B11_15 P11.constantEigenvector
  ≡ P11.scalePair (+ 24) P11.constantEigenvector
B15ConstantEigenvalueTwentyFour = refl

B15NonconstantEigenvalueMinusOne :
  Brandt.matrixAction B11_15 P11.nonconstantEigenvector
  ≡ P11.scalePair (-[1+ 0 ]) P11.nonconstantEigenvector
B15NonconstantEigenvalueMinusOne = refl

B2Squared : Brandt.P11BrandtMatrix
B2Squared = compose Brandt.B11_2 Brandt.B11_2

B2SquaredMatrixExact :
  B2Squared ≡ Brandt.brandtMatrix 6 3 2 7
B2SquaredMatrixExact = refl

fullT4Matrix : Brandt.P11BrandtMatrix
fullT4Matrix = Brandt.brandtMatrix 4 3 2 5

B2SquaredEqualsFullT4Plus2IOnJ0 :
  Brandt.matrixAction B2Squared Spectral.basisJ0
  ≡ Square.addPair
      (Brandt.matrixAction fullT4Matrix Spectral.basisJ0)
      (P11.scalePair (+ 2) Spectral.basisJ0)
B2SquaredEqualsFullT4Plus2IOnJ0 = refl

B2SquaredEqualsFullT4Plus2IOnJ1 :
  Brandt.matrixAction B2Squared Spectral.basisJ1
  ≡ Square.addPair
      (Brandt.matrixAction fullT4Matrix Spectral.basisJ1)
      (P11.scalePair (+ 2) Spectral.basisJ1)
B2SquaredEqualsFullT4Plus2IOnJ1 = refl

fullT4MatchesPR567ForcedOnJ0 :
  Brandt.matrixAction fullT4Matrix Spectral.basisJ0
  ≡ Square.forcedT4Action Spectral.basisJ0
fullT4MatchesPR567ForcedOnJ0 = refl

fullT4MatchesPR567ForcedOnJ1 :
  Brandt.matrixAction fullT4Matrix Spectral.basisJ1
  ≡ Square.forcedT4Action Spectral.basisJ1
fullT4MatchesPR567ForcedOnJ1 = refl

B5MatchesCyclicPhi4OnJ0 :
  Brandt.matrixAction Brandt.B11_5 Spectral.basisJ0
  ≡ Phi4.cyclicFourMatrixAction Spectral.basisJ0
B5MatchesCyclicPhi4OnJ0 = refl

B5MatchesCyclicPhi4OnJ1 :
  Brandt.matrixAction Brandt.B11_5 Spectral.basisJ1
  ≡ Phi4.cyclicFourMatrixAction Spectral.basisJ1
B5MatchesCyclicPhi4OnJ1 = refl

B5MatchesCyclicPhi4ConstantMode :
  Brandt.matrixAction Brandt.B11_5 P11.constantEigenvector
  ≡ Phi4.cyclicFourMatrixAction P11.constantEigenvector
B5MatchesCyclicPhi4ConstantMode = refl

B5MatchesCyclicPhi4NonconstantMode :
  Brandt.matrixAction Brandt.B11_5 P11.nonconstantEigenvector
  ≡ Phi4.cyclicFourMatrixAction P11.nonconstantEigenvector
B5MatchesCyclicPhi4NonconstantMode = refl

record P11BrandtJointHeckeBoundary : Set where
  field
    threePrimeGeneratorsShareJointEigenbasis : Bool
    threePrimeGeneratorsShareJointEigenbasisIsTrue :
      threePrimeGeneratorsShareJointEigenbasis ≡ true

    pairwiseCoprimeGeneratorCommutationConstructed : Bool
    pairwiseCoprimeGeneratorCommutationConstructedIsTrue :
      pairwiseCoprimeGeneratorCommutationConstructed ≡ true

    ell2PrimeSquareRelationConstructed : Bool
    ell2PrimeSquareRelationConstructedIsTrue :
      ell2PrimeSquareRelationConstructed ≡ true

    b5AndCyclicPhi4HaveSameTwoStateMatrix : Bool
    b5AndCyclicPhi4HaveSameTwoStateMatrixIsTrue :
      b5AndCyclicPhi4HaveSameTwoStateMatrix ≡ true

    sameTwoStateMatrixPromotedToSameGeometricCorrespondence : Bool
    sameTwoStateMatrixPromotedToSameGeometricCorrespondenceIsFalse :
      sameTwoStateMatrixPromotedToSameGeometricCorrespondence ≡ false

    representationSideJointHeckeIntertwinerConstructedHere : Bool
    representationSideJointHeckeIntertwinerConstructedHereIsFalse :
      representationSideJointHeckeIntertwinerConstructedHere ≡ false

canonicalP11BrandtJointHeckeBoundary : P11BrandtJointHeckeBoundary
canonicalP11BrandtJointHeckeBoundary =
  record
    { threePrimeGeneratorsShareJointEigenbasis = true
    ; threePrimeGeneratorsShareJointEigenbasisIsTrue = refl
    ; pairwiseCoprimeGeneratorCommutationConstructed = true
    ; pairwiseCoprimeGeneratorCommutationConstructedIsTrue = refl
    ; ell2PrimeSquareRelationConstructed = true
    ; ell2PrimeSquareRelationConstructedIsTrue = refl
    ; b5AndCyclicPhi4HaveSameTwoStateMatrix = true
    ; b5AndCyclicPhi4HaveSameTwoStateMatrixIsTrue = refl
    ; sameTwoStateMatrixPromotedToSameGeometricCorrespondence = false
    ; sameTwoStateMatrixPromotedToSameGeometricCorrespondenceIsFalse = refl
    ; representationSideJointHeckeIntertwinerConstructedHere = false
    ; representationSideJointHeckeIntertwinerConstructedHereIsFalse = refl
    }
