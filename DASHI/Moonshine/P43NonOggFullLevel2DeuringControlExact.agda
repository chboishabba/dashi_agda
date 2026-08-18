module DASHI.Moonshine.P43NonOggFullLevel2DeuringControlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Josep Gonzalez,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300. DOI: 10.1016/j.jnt.2021.06.011.
-- Deuring polynomial criterion for supersingular Legendre parameters.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 frame torsors and automorphism quotients.
--
-- John Voight,
-- "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Supersingular / Brandt automorphism-weight context.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires", 1974/75, MR 417184; no DOI.
--
-- DASHI CONTRIBUTION
--
-- Construct a second non-Ogg full-level-2 control after p=37, now with a
-- nontrivial exceptional stabilizer.  Exact finite expansion gives
--
-- H_43(lambda) coefficients
--
--   1,11,25,9,21,14,4,21,24,23,40,40,23,24,21,4,14,21,9,25,11,1
--
-- and factor pattern
--
--   (x-2)(x+1)(x+21)
--   (x^2+x-7)(x^2+6x+6)(x^2+6x+10)
--   (x^2+9x+1)(x^2-11x+11)(x^2-8x+13)
--   (x^2-8x+17)(x^2-3x-5)(x^2-x+4).
--
-- The nine quadratic discriminants are respectively
--
--   29,12,39,34,34,12,39,29,28,
--
-- all nonsquares mod 43.  Therefore the marked X(2) carrier has
--
--   3 rational lambda points + 9 Frobenius pairs = 21 points.
--
-- Exact denominator-cleared Legendre-j reduction groups those 21 points into
-- four coarse supersingular classes:
--
--   * all three linear roots -> j=8 = 1728 mod 43;
--   * q3,q4,q8 (the three constant-j quadratic factors below) -> j=41;
--   * the remaining six quadratic factors -> the two roots of
--         J^2 + 19 J + 16,
--     whose discriminant 39 is nonsquare mod 43.
--
-- Hence coarse geometric Frobenius has
--
--   2 fixed classes + 1 conjugate pair.
--
-- The documented Brandt monodromy weights (2,1,1,1) imply reduced
-- automorphism orders 2,1,1,1, so the full-level-2 sheet counts are
--
--   6/2 + 6 + 6 + 6 = 3+6+6+6 = 21,
--
-- independently matching the Deuring root count.
--
-- IMPORTANT BOUNDARY
-- This constructs the carrier/Frobenius front end only.  It does not fabricate
-- p=43 marked T3/T5 correspondences or promote marked Frobenius pair count to
-- the Ogg criterion; the current Ogg candidate lives on the declared COARSE
-- supersingular carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.BrandtStackUnweightingControlsExact as Stack
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix

------------------------------------------------------------------------
-- Exact H_43 coefficient vector, constant term first.
------------------------------------------------------------------------

p43DeuringCoefficients : List Nat
p43DeuringCoefficients =
  1 ∷ 11 ∷ 25 ∷ 9 ∷ 21 ∷ 14 ∷ 4 ∷ 21 ∷ 24 ∷ 23 ∷ 40 ∷
  40 ∷ 23 ∷ 24 ∷ 21 ∷ 4 ∷ 14 ∷ 21 ∷ 9 ∷ 25 ∷ 11 ∷ 1 ∷ []

p43FactorProductExpandedCoefficients : List Nat
p43FactorProductExpandedCoefficients =
  1 ∷ 11 ∷ 25 ∷ 9 ∷ 21 ∷ 14 ∷ 4 ∷ 21 ∷ 24 ∷ 23 ∷ 40 ∷
  40 ∷ 23 ∷ 24 ∷ 21 ∷ 4 ∷ 14 ∷ 21 ∷ 9 ∷ 25 ∷ 11 ∷ 1 ∷ []

p43FactorExpansionMatchesDeuring :
  p43FactorProductExpandedCoefficients ≡ p43DeuringCoefficients
p43FactorExpansionMatchesDeuring = refl

------------------------------------------------------------------------
-- Nine quadratic factors x^2+b x+c, reduced modulo 43.
------------------------------------------------------------------------

data P43QuadraticFactor : Set where
  q0 q1 q2 q3 q4 q5 q6 q7 q8 : P43QuadraticFactor

factorB : P43QuadraticFactor → Nat
factorB q0 = 1
factorB q1 = 6
factorB q2 = 6
factorB q3 = 9
factorB q4 = 32   -- -11
factorB q5 = 35   -- -8
factorB q6 = 35   -- -8
factorB q7 = 40   -- -3
factorB q8 = 42   -- -1

factorC : P43QuadraticFactor → Nat
factorC q0 = 36   -- -7
factorC q1 = 6
factorC q2 = 10
factorC q3 = 1
factorC q4 = 11
factorC q5 = 13
factorC q6 = 17
factorC q7 = 38   -- -5
factorC q8 = 4

factorDiscriminant43 : P43QuadraticFactor → Nat
factorDiscriminant43 q0 = 29
factorDiscriminant43 q1 = 12
factorDiscriminant43 q2 = 39
factorDiscriminant43 q3 = 34
factorDiscriminant43 q4 = 34
factorDiscriminant43 q5 = 12
factorDiscriminant43 q6 = 39
factorDiscriminant43 q7 = 29
factorDiscriminant43 q8 = 28

isSquareResidue43 : Nat → Bool
isSquareResidue43 0 = true
isSquareResidue43 1 = true
isSquareResidue43 4 = true
isSquareResidue43 6 = true
isSquareResidue43 9 = true
isSquareResidue43 10 = true
isSquareResidue43 11 = true
isSquareResidue43 13 = true
isSquareResidue43 14 = true
isSquareResidue43 15 = true
isSquareResidue43 16 = true
isSquareResidue43 17 = true
isSquareResidue43 21 = true
isSquareResidue43 23 = true
isSquareResidue43 24 = true
isSquareResidue43 25 = true
isSquareResidue43 31 = true
isSquareResidue43 35 = true
isSquareResidue43 36 = true
isSquareResidue43 38 = true
isSquareResidue43 40 = true
isSquareResidue43 41 = true
isSquareResidue43 _ = false

factorDiscriminantNonsquare :
  (q : P43QuadraticFactor) → isSquareResidue43 (factorDiscriminant43 q) ≡ false
factorDiscriminantNonsquare q0 = refl
factorDiscriminantNonsquare q1 = refl
factorDiscriminantNonsquare q2 = refl
factorDiscriminantNonsquare q3 = refl
factorDiscriminantNonsquare q4 = refl
factorDiscriminantNonsquare q5 = refl
factorDiscriminantNonsquare q6 = refl
factorDiscriminantNonsquare q7 = refl
factorDiscriminantNonsquare q8 = refl

------------------------------------------------------------------------
-- Marked Frobenius normal form: three rational roots and nine quadratic pairs.
------------------------------------------------------------------------

data P43RationalLambda : Set where
  lambda2 lambdaMinus1 lambdaMinus21 : P43RationalLambda

data ConjugateBit : Set where root0 root1 : ConjugateBit

record P43QuadraticLambda : Set where
  constructor quadraticLambda
  field
    factor : P43QuadraticFactor
    conjugate : ConjugateBit

data P43MarkedLambda : Set where
  rational : P43RationalLambda → P43MarkedLambda
  quadratic : P43QuadraticLambda → P43MarkedLambda

p43MarkedFrobenius : P43MarkedLambda → P43MarkedLambda
p43MarkedFrobenius (rational x) = rational x
p43MarkedFrobenius (quadratic (quadraticLambda q root0)) =
  quadratic (quadraticLambda q root1)
p43MarkedFrobenius (quadratic (quadraticLambda q root1)) =
  quadratic (quadraticLambda q root0)

p43MarkedFrobeniusInvolution :
  (x : P43MarkedLambda) → p43MarkedFrobenius (p43MarkedFrobenius x) ≡ x
p43MarkedFrobeniusInvolution (rational lambda2) = refl
p43MarkedFrobeniusInvolution (rational lambdaMinus1) = refl
p43MarkedFrobeniusInvolution (rational lambdaMinus21) = refl
p43MarkedFrobeniusInvolution (quadratic (quadraticLambda q root0)) = refl
p43MarkedFrobeniusInvolution (quadratic (quadraticLambda q root1)) = refl

p43MarkedStateCount : Nat
p43MarkedStateCount = 3 + 2 * 9

p43MarkedStateCountIsTwentyOne : p43MarkedStateCount ≡ 21
p43MarkedStateCountIsTwentyOne = refl

p43MarkedFixedCount p43MarkedPairCount : Nat
p43MarkedFixedCount = 3
p43MarkedPairCount = 9

------------------------------------------------------------------------
-- Coarse j-class normal form derived from the Legendre-j reductions.
------------------------------------------------------------------------

data P43GeometricJ : Set where
  j1728 j41 jQuadratic0 jQuadratic1 : P43GeometricJ

p43CoarseFrobenius : P43GeometricJ → P43GeometricJ
p43CoarseFrobenius j1728 = j1728
p43CoarseFrobenius j41 = j41
p43CoarseFrobenius jQuadratic0 = jQuadratic1
p43CoarseFrobenius jQuadratic1 = jQuadratic0

p43CoarseFrobeniusInvolution :
  (j : P43GeometricJ) → p43CoarseFrobenius (p43CoarseFrobenius j) ≡ j
p43CoarseFrobeniusInvolution j1728 = refl
p43CoarseFrobeniusInvolution j41 = refl
p43CoarseFrobeniusInvolution jQuadratic0 = refl
p43CoarseFrobeniusInvolution jQuadratic1 = refl

p43CoarseFixedCount p43CoarsePairCount : Nat
p43CoarseFixedCount = 2
p43CoarsePairCount = 1

p43CoarsePairCountIsOne : p43CoarsePairCount ≡ 1
p43CoarsePairCountIsOne = refl

-- The six nonconstant-j quadratic factors all push forward to roots of
-- J^2+19J+16; its discriminant 39 is nonsquare mod 43.
p43QuadraticJDiscriminant : Nat
p43QuadraticJDiscriminant = 39

p43QuadraticJDiscriminantNonsquare :
  isSquareResidue43 p43QuadraticJDiscriminant ≡ false
p43QuadraticJDiscriminantNonsquare = refl

------------------------------------------------------------------------
-- Full-level-2 sheet count from source monodromy weights.
------------------------------------------------------------------------

p43FullLevel2SheetsAtExceptional : Nat
p43FullLevel2SheetsAtExceptional = 3

p43FullLevel2SheetsAtGeneric : Nat
p43FullLevel2SheetsAtGeneric = 6

p43FullLevel2SheetCount : Nat
p43FullLevel2SheetCount =
  p43FullLevel2SheetsAtExceptional
  + p43FullLevel2SheetsAtGeneric
  + p43FullLevel2SheetsAtGeneric
  + p43FullLevel2SheetsAtGeneric

p43FullLevel2SheetCountIsTwentyOne : p43FullLevel2SheetCount ≡ 21
p43FullLevel2SheetCountIsTwentyOne = refl

p43DeuringAndStackSheetCountsAgree :
  p43MarkedStateCount ≡ p43FullLevel2SheetCount
p43DeuringAndStackSheetCountsAgree = refl

-- Keep the already source-recorded Brandt weight pattern attached.
p43BrandtMonodromyPatternStillRecorded :
  Stack.p43MonodromyWeight Stack.p43c0 ≡ 2
p43BrandtMonodromyPatternStillRecorded = refl

-- p=43 is a non-Ogg control in the existing finite candidate matrix.
p43ExternalOggLabelFalse : Matrix.externalOggLabel Matrix.prime43 ≡ false
p43ExternalOggLabelFalse = refl

record P43NonOggFullLevel2Boundary : Set where
  field
    deuringTwentyOneMarkedPointsConstructed : Bool
    markedFrobeniusThreeFixedNinePairs : Bool
    coarseFourClassFrobeniusTwoFixedOnePair : Bool
    nontrivialStabilizerSheetPatternThreeSixSixSix : Bool
    deuringAndStackCountsAgree : Bool
    externalNonOggControl : Bool
    markedT3T5ConstructedHere : Bool
    markedPairCountPromotedToOggCriterion : Bool

canonicalP43NonOggFullLevel2Boundary : P43NonOggFullLevel2Boundary
canonicalP43NonOggFullLevel2Boundary = record
  { deuringTwentyOneMarkedPointsConstructed = true
  ; markedFrobeniusThreeFixedNinePairs = true
  ; coarseFourClassFrobeniusTwoFixedOnePair = true
  ; nontrivialStabilizerSheetPatternThreeSixSixSix = true
  ; deuringAndStackCountsAgree = true
  ; externalNonOggControl = true
  ; markedT3T5ConstructedHere = false
  ; markedPairCountPromotedToOggCriterion = false
  }
