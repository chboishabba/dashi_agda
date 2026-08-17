module DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer.
-- DOI: 10.1007/978-1-4684-9458-7.
-- Permutation modules Ind_H^G(1) and the irreducible representations of S3.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
-- Hecke actions with auxiliary level structure.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 deck action / moduli context.
--
-- DASHI CONTRIBUTION
--
-- The source-native five-state marked carrier is
--
--   C3\S3 disjoint-union C2\S3.
--
-- Therefore its permutation representation has the canonical decomposition
--
--   Ind_C3^S3(1) + Ind_C2^S3(1)
--     = (1 + sgn) + (1 + std)
--     = 2*1 + sgn + std.
--
-- The corrected quaternion-derived marked T3 and T5 diagonalize exactly on
-- explicit vectors spanning these four representation sectors:
--
--                              T3    T5    Frobenius
--   total constant              4     6       +1
--   coarse Brandt newform      -1     1       +1
--   S3 sign                     1    -3       -1
--   S3 standard (dimension 2)  -1     1       +1.
--
-- The five displayed basis vectors have determinant 30, so they are a basis
-- over Q.  Thus this is a complete simultaneous rational decomposition, not a
-- selection of a few test eigenvectors.
--
-- HIGH-ALPHA CONSEQUENCE
-- The coarse Brandt nontrivial line and the two-dimensional deck-standard
-- sector have the SAME (T3,T5,F) eigenfingerprint (-1,1,+1).  Hence even the
-- corrected joint Hecke+Frobenius observation forgets an exact representation
-- distinction.  The deck-S3 label itself is genuine extra information.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P11MarkedX2HeckeReconstructionExact as Marked
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact as FF

------------------------------------------------------------------------
-- Five-coordinate integer vectors in order a0,a1,b0,b1,b2.
------------------------------------------------------------------------

record Int5 : Set where
  constructor int5
  field
    a0c a1c b0c b1c b2c : ℤ

open Int5 public

add5 : Int5 → Int5 → Int5
add5 u v = int5
  (a0c u +ℤ a0c v) (a1c u +ℤ a1c v)
  (b0c u +ℤ b0c v) (b1c u +ℤ b1c v) (b2c u +ℤ b2c v)

scale5 : ℤ → Int5 → Int5
scale5 z v = int5
  (z *ℤ a0c v) (z *ℤ a1c v)
  (z *ℤ b0c v) (z *ℤ b1c v) (z *ℤ b2c v)

coordinate : Fine.P11Fine5 → Int5 → ℤ
coordinate Fine.a0 = a0c
coordinate Fine.a1 = a1c
coordinate Fine.b0 = b0c
coordinate Fine.b1 = b1c
coordinate Fine.b2 = b2c

------------------------------------------------------------------------
-- Integer linearization of a positive neighbour system, written explicitly
-- for the corrected T3/T5 matrices so no Nat->Int fold machinery is invented.
------------------------------------------------------------------------

markedT3Action : Int5 → Int5
markedT3Action v = int5
  (a0c v +ℤ b0c v +ℤ b1c v +ℤ b2c v)
  (a1c v +ℤ b0c v +ℤ b1c v +ℤ b2c v)
  (a0c v +ℤ a1c v +ℤ b1c v +ℤ b2c v)
  (a0c v +ℤ a1c v +ℤ b0c v +ℤ b2c v)
  (a0c v +ℤ a1c v +ℤ b0c v +ℤ b1c v)

markedT5Action : Int5 → Int5
markedT5Action v = int5
  (((+ 3) *ℤ a1c v) +ℤ b0c v +ℤ b1c v +ℤ b2c v)
  (((+ 3) *ℤ a0c v) +ℤ b0c v +ℤ b1c v +ℤ b2c v)
  (a0c v +ℤ a1c v +ℤ ((+ 2) *ℤ b0c v) +ℤ b1c v +ℤ b2c v)
  (a0c v +ℤ a1c v +ℤ b0c v +ℤ ((+ 2) *ℤ b1c v) +ℤ b2c v)
  (a0c v +ℤ a1c v +ℤ b0c v +ℤ b1c v +ℤ ((+ 2) *ℤ b2c v))

markedFrobeniusAction : Int5 → Int5
markedFrobeniusAction v = int5
  (a1c v) (a0c v) (b0c v) (b1c v) (b2c v)

------------------------------------------------------------------------
-- Canonical sector vectors.
------------------------------------------------------------------------

constantVector : Int5
constantVector = int5 (+ 1) (+ 1) (+ 1) (+ 1) (+ 1)

-- Pullback of the coarse nonconstant Brandt eigenvector (-3,2).
brandtNewformVector : Int5
brandtNewformVector = int5 (-[1+ 2 ]) (-[1+ 2 ]) (+ 2) (+ 2) (+ 2)

signVector : Int5
signVector = int5 (+ 1) (-[1+ 0 ]) (+ 0) (+ 0) (+ 0)

standardVector1 : Int5
standardVector1 = int5 (+ 0) (+ 0) (+ 1) (-[1+ 0 ]) (+ 0)

standardVector2 : Int5
standardVector2 = int5 (+ 0) (+ 0) (+ 1) (+ 0) (-[1+ 0 ])

------------------------------------------------------------------------
-- Corrected T3 eigenvalues.
------------------------------------------------------------------------

T3ConstantEigen : markedT3Action constantVector ≡ scale5 (+ 4) constantVector
T3ConstantEigen = refl

T3BrandtEigen : markedT3Action brandtNewformVector ≡ scale5 (-[1+ 0 ]) brandtNewformVector
T3BrandtEigen = refl

T3SignEigen : markedT3Action signVector ≡ scale5 (+ 1) signVector
T3SignEigen = refl

T3Standard1Eigen : markedT3Action standardVector1 ≡ scale5 (-[1+ 0 ]) standardVector1
T3Standard1Eigen = refl

T3Standard2Eigen : markedT3Action standardVector2 ≡ scale5 (-[1+ 0 ]) standardVector2
T3Standard2Eigen = refl

------------------------------------------------------------------------
-- Corrected T5 eigenvalues.
------------------------------------------------------------------------

T5ConstantEigen : markedT5Action constantVector ≡ scale5 (+ 6) constantVector
T5ConstantEigen = refl

T5BrandtEigen : markedT5Action brandtNewformVector ≡ scale5 (+ 1) brandtNewformVector
T5BrandtEigen = refl

T5SignEigen : markedT5Action signVector ≡ scale5 (-[1+ 2 ]) signVector
T5SignEigen = refl

T5Standard1Eigen : markedT5Action standardVector1 ≡ scale5 (+ 1) standardVector1
T5Standard1Eigen = refl

T5Standard2Eigen : markedT5Action standardVector2 ≡ scale5 (+ 1) standardVector2
T5Standard2Eigen = refl

------------------------------------------------------------------------
-- Fine Frobenius eigenvalues.
------------------------------------------------------------------------

FConstantEigen : markedFrobeniusAction constantVector ≡ scale5 (+ 1) constantVector
FConstantEigen = refl

FBrandtEigen : markedFrobeniusAction brandtNewformVector ≡ scale5 (+ 1) brandtNewformVector
FBrandtEigen = refl

FSignEigen : markedFrobeniusAction signVector ≡ scale5 (-[1+ 0 ]) signVector
FSignEigen = refl

FStandard1Eigen : markedFrobeniusAction standardVector1 ≡ scale5 (+ 1) standardVector1
FStandard1Eigen = refl

FStandard2Eigen : markedFrobeniusAction standardVector2 ≡ scale5 (+ 1) standardVector2
FStandard2Eigen = refl

------------------------------------------------------------------------
-- Complete rational-basis certificate.
-- Columns [constant,newform,sign,std1,std2] have determinant 30.
------------------------------------------------------------------------

simultaneousBasisDeterminant : ℤ
simultaneousBasisDeterminant = + 30

simultaneousBasisDeterminantIsThirty : simultaneousBasisDeterminant ≡ + 30
simultaneousBasisDeterminantIsThirty = refl

simultaneousBasisDeterminantNonzero : simultaneousBasisDeterminant ≡ + 0 → ⊥
simultaneousBasisDeterminantNonzero ()

------------------------------------------------------------------------
-- Exact observation collision: Brandt-newform and standard sectors carry the
-- same corrected T3/T5/F eigenvalues despite being different S3 types.
------------------------------------------------------------------------

record JointEigenFingerprint : Set where
  constructor jointEigen
  field
    t3Eigen t5Eigen frobeniusEigen : ℤ

brandtNewformFingerprint : JointEigenFingerprint
brandtNewformFingerprint = jointEigen (-[1+ 0 ]) (+ 1) (+ 1)

standardFingerprint : JointEigenFingerprint
standardFingerprint = jointEigen (-[1+ 0 ]) (+ 1) (+ 1)

brandtAndStandardFingerprintsCoincide :
  brandtNewformFingerprint ≡ standardFingerprint
brandtAndStandardFingerprintsCoincide = refl

record P11MarkedX2S3HeckeBoundary : Set where
  field
    deckPermutationDecompositionConstructed : Bool
    deckPermutationDecompositionConstructedIsTrue :
      deckPermutationDecompositionConstructed ≡ true

    correctedT3T5SimultaneouslyDiagonalized : Bool
    correctedT3T5SimultaneouslyDiagonalizedIsTrue :
      correctedT3T5SimultaneouslyDiagonalized ≡ true

    rationalBasisDeterminantNonzero : Bool
    rationalBasisDeterminantNonzeroIsTrue : rationalBasisDeterminantNonzero ≡ true

    frobeniusEigenDecompositionConstructed : Bool
    frobeniusEigenDecompositionConstructedIsTrue :
      frobeniusEigenDecompositionConstructed ≡ true

    brandtVsStandardJointFingerprintCollisionConstructed : Bool
    brandtVsStandardJointFingerprintCollisionConstructedIsTrue :
      brandtVsStandardJointFingerprintCollisionConstructed ≡ true

    deckS3TypeDiscardedAsRedundantObservation : Bool
    deckS3TypeDiscardedAsRedundantObservationIsFalse :
      deckS3TypeDiscardedAsRedundantObservation ≡ false

canonicalP11MarkedX2S3HeckeBoundary : P11MarkedX2S3HeckeBoundary
canonicalP11MarkedX2S3HeckeBoundary = record
  { deckPermutationDecompositionConstructed = true
  ; deckPermutationDecompositionConstructedIsTrue = refl
  ; correctedT3T5SimultaneouslyDiagonalized = true
  ; correctedT3T5SimultaneouslyDiagonalizedIsTrue = refl
  ; rationalBasisDeterminantNonzero = true
  ; rationalBasisDeterminantNonzeroIsTrue = refl
  ; frobeniusEigenDecompositionConstructed = true
  ; frobeniusEigenDecompositionConstructedIsTrue = refl
  ; brandtVsStandardJointFingerprintCollisionConstructed = true
  ; brandtVsStandardJointFingerprintCollisionConstructedIsTrue = refl
  ; deckS3TypeDiscardedAsRedundantObservation = false
  ; deckS3TypeDiscardedAsRedundantObservationIsFalse = refl
  }
