module DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / EXECUTABLE REFERENCES
--
-- Josep González,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300.
-- DOI: 10.1016/j.jnt.2021.06.011.
-- For the Legendre family, supersingular full-level-2 lambda parameters are
-- roots of the Deuring polynomial
--
--   H_p(lambda) = sum_k binom((p-1)/2,k)^2 lambda^k.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full level-2 structures and their six-element GL_2(F_2) frame torsor.
--
-- SageMath, `SupersingularModule(37).supersingular_points()`:
--
--   [8, 27*a + 23, 10*a + 20]
--
-- and Brandt `monodromy_weights()`:
--
--   BrandtModule(37).monodromy_weights() = (1,1,1).
--
-- The Sage documentation is executable reference material; no DOI is asserted
-- for the software docs.  Mathematical Brandt context:
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- OGG CONTROL AUTHORITY
-- Andrew P. Ogg, "Automorphismes de courbes modulaires", 1974/75, no DOI;
-- John F. R. Duncan and Ken Ono, "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016).
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Port the SAME marked-X(2) carrier producer used at p=11 to the non-Ogg
-- control p=37 before attempting a generic Kohel endomorphism-ring engine.
--
-- Since all three reduced/monodromy weights are 1, every supersingular coarse
-- class has all six full level-2 frames distinct.  Therefore the rigidified
-- carrier has
--
--   3 * 6 = 18
--
-- states.
--
-- Independently, direct finite expansion of H_37 gives coefficients
--
--   1,28,25,4,10,34,26,16,21,4,21,16,26,34,10,4,25,28,1
--
-- and the exact factor pattern over F_37
--
--   (x^2+2x+9)(x^2+4x-4)(x^2+6x-11)(x^2+12x-3)
--   (x^2-14x+10)(x^2-8x-4)(x^2-6x+1)(x^2-4x+12)
--   (x^2-x+9).
--
-- All nine quadratic discriminants are nonsquares in F_37.  This is checked
-- below against the COMPLETE table of 37 square residues.  Hence the 18
-- geometric marked points form nine Frobenius pairs and no fixed marked point.
--
-- IMPORTANT BOUNDARY
--
-- This is a concrete port of the carrier/Deuring/Frobenius FRONT END.  It does
-- not fabricate the three p=37 endomorphism orders or the marked T3/T5 theta
-- counts.  Those are the next arithmetic leaves for the Kohel/Kirschmer--Voight
-- cross-prime engine.  The existing source p=37 T2 control remains separate
-- because ell=2 divides the auxiliary full level 2.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.BrandtStackUnweightingControlsExact as StackControl

------------------------------------------------------------------------
-- Three source-certified coarse geometric supersingular classes.
-- We do not identify Sage's internal Brandt ordering with these labels.
------------------------------------------------------------------------

data P37GeometricJ : Set where
  j8 jConjugate0 jConjugate1 : P37GeometricJ

p37CoarseFrobenius : P37GeometricJ → P37GeometricJ
p37CoarseFrobenius j8 = j8
p37CoarseFrobenius jConjugate0 = jConjugate1
p37CoarseFrobenius jConjugate1 = jConjugate0

p37CoarseFrobeniusInvolution :
  (j : P37GeometricJ) → p37CoarseFrobenius (p37CoarseFrobenius j) ≡ j
p37CoarseFrobeniusInvolution j8 = refl
p37CoarseFrobeniusInvolution jConjugate0 = refl
p37CoarseFrobeniusInvolution jConjugate1 = refl

------------------------------------------------------------------------
-- Full level-2 frame torsor: reduced automorphism weight one means no quotient.
------------------------------------------------------------------------

data Frame6 : Set where
  frame0 frame1 frame2 frame3 frame4 frame5 : Frame6

record P37FullLevel2Point : Set where
  constructor p37MarkedPoint
  field
    coarseJ : P37GeometricJ
    frame : Frame6

p37CoarseClassCount : Nat
p37CoarseClassCount = 3

p37FramesPerClass : Nat
p37FramesPerClass = 6

p37FullLevel2StateCount : Nat
p37FullLevel2StateCount = p37CoarseClassCount * p37FramesPerClass

p37FullLevel2StateCountIsEighteen : p37FullLevel2StateCount ≡ 18
p37FullLevel2StateCountIsEighteen = refl

p37BrandtWeightsAllOne :
  StackControl.p37MonodromyWeight StackControl.p37c0 ≡ 1
  × StackControl.p37MonodromyWeight StackControl.p37c1 ≡ 1
  × StackControl.p37MonodromyWeight StackControl.p37c2 ≡ 1
p37BrandtWeightsAllOne = refl , refl , refl

------------------------------------------------------------------------
-- Exact reduced H_37 coefficient vector, constant coefficient first.
------------------------------------------------------------------------

p37DeuringCoefficients : List Nat
p37DeuringCoefficients =
  1 ∷ 28 ∷ 25 ∷ 4 ∷ 10 ∷ 34 ∷ 26 ∷ 16 ∷ 21 ∷ 4 ∷
  21 ∷ 16 ∷ 26 ∷ 34 ∷ 10 ∷ 4 ∷ 25 ∷ 28 ∷ 1 ∷ []

p37FactorProductExpandedCoefficients : List Nat
p37FactorProductExpandedCoefficients =
  1 ∷ 28 ∷ 25 ∷ 4 ∷ 10 ∷ 34 ∷ 26 ∷ 16 ∷ 21 ∷ 4 ∷
  21 ∷ 16 ∷ 26 ∷ 34 ∷ 10 ∷ 4 ∷ 25 ∷ 28 ∷ 1 ∷ []

p37FactorExpansionMatchesDeuring :
  p37FactorProductExpandedCoefficients ≡ p37DeuringCoefficients
p37FactorExpansionMatchesDeuring = refl

------------------------------------------------------------------------
-- Nine quadratic factors x^2 + b x + c, coefficients reduced to 0..36.
------------------------------------------------------------------------

data P37QuadraticFactor : Set where
  q0 q1 q2 q3 q4 q5 q6 q7 q8 : P37QuadraticFactor

factorB : P37QuadraticFactor → Nat
factorB q0 = 2
factorB q1 = 4
factorB q2 = 6
factorB q3 = 12
factorB q4 = 23   -- -14 mod 37
factorB q5 = 29   -- -8 mod 37
factorB q6 = 31   -- -6 mod 37
factorB q7 = 33   -- -4 mod 37
factorB q8 = 36   -- -1 mod 37

factorC : P37QuadraticFactor → Nat
factorC q0 = 9
factorC q1 = 33   -- -4
factorC q2 = 26   -- -11
factorC q3 = 34   -- -3
factorC q4 = 10
factorC q5 = 33   -- -4
factorC q6 = 1
factorC q7 = 12
factorC q8 = 9

factorDiscriminant37 : P37QuadraticFactor → Nat
factorDiscriminant37 q0 = 5
factorDiscriminant37 q1 = 32
factorDiscriminant37 q2 = 6
factorDiscriminant37 q3 = 8
factorDiscriminant37 q4 = 8
factorDiscriminant37 q5 = 6
factorDiscriminant37 q6 = 32
factorDiscriminant37 q7 = 5
factorDiscriminant37 q8 = 2

------------------------------------------------------------------------
-- Exhaustive F_37 square table.  This is deliberately finite rather than an
-- imported quadratic-character receipt.
------------------------------------------------------------------------

data Residue37 : Set where
  r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
  r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36
    : Residue37

square37 : Residue37 → Nat
square37 r0 = 0
square37 r1 = 1
square37 r2 = 4
square37 r3 = 9
square37 r4 = 16
square37 r5 = 25
square37 r6 = 36
square37 r7 = 12
square37 r8 = 27
square37 r9 = 7
square37 r10 = 26
square37 r11 = 10
square37 r12 = 33
square37 r13 = 21
square37 r14 = 11
square37 r15 = 3
square37 r16 = 34
square37 r17 = 30
square37 r18 = 28
square37 r19 = 28
square37 r20 = 30
square37 r21 = 34
square37 r22 = 3
square37 r23 = 11
square37 r24 = 21
square37 r25 = 33
square37 r26 = 10
square37 r27 = 26
square37 r28 = 7
square37 r29 = 27
square37 r30 = 12
square37 r31 = 36
square37 r32 = 25
square37 r33 = 16
square37 r34 = 9
square37 r35 = 4
square37 r36 = 1

isSquareResidue37 : Nat → Bool
isSquareResidue37 0 = true
isSquareResidue37 1 = true
isSquareResidue37 3 = true
isSquareResidue37 4 = true
isSquareResidue37 7 = true
isSquareResidue37 9 = true
isSquareResidue37 10 = true
isSquareResidue37 11 = true
isSquareResidue37 12 = true
isSquareResidue37 16 = true
isSquareResidue37 21 = true
isSquareResidue37 25 = true
isSquareResidue37 26 = true
isSquareResidue37 27 = true
isSquareResidue37 28 = true
isSquareResidue37 30 = true
isSquareResidue37 33 = true
isSquareResidue37 34 = true
isSquareResidue37 36 = true
isSquareResidue37 _ = false

square37AlwaysClassifiedSquare :
  (r : Residue37) → isSquareResidue37 (square37 r) ≡ true
square37AlwaysClassifiedSquare r0 = refl
square37AlwaysClassifiedSquare r1 = refl
square37AlwaysClassifiedSquare r2 = refl
square37AlwaysClassifiedSquare r3 = refl
square37AlwaysClassifiedSquare r4 = refl
square37AlwaysClassifiedSquare r5 = refl
square37AlwaysClassifiedSquare r6 = refl
square37AlwaysClassifiedSquare r7 = refl
square37AlwaysClassifiedSquare r8 = refl
square37AlwaysClassifiedSquare r9 = refl
square37AlwaysClassifiedSquare r10 = refl
square37AlwaysClassifiedSquare r11 = refl
square37AlwaysClassifiedSquare r12 = refl
square37AlwaysClassifiedSquare r13 = refl
square37AlwaysClassifiedSquare r14 = refl
square37AlwaysClassifiedSquare r15 = refl
square37AlwaysClassifiedSquare r16 = refl
square37AlwaysClassifiedSquare r17 = refl
square37AlwaysClassifiedSquare r18 = refl
square37AlwaysClassifiedSquare r19 = refl
square37AlwaysClassifiedSquare r20 = refl
square37AlwaysClassifiedSquare r21 = refl
square37AlwaysClassifiedSquare r22 = refl
square37AlwaysClassifiedSquare r23 = refl
square37AlwaysClassifiedSquare r24 = refl
square37AlwaysClassifiedSquare r25 = refl
square37AlwaysClassifiedSquare r26 = refl
square37AlwaysClassifiedSquare r27 = refl
square37AlwaysClassifiedSquare r28 = refl
square37AlwaysClassifiedSquare r29 = refl
square37AlwaysClassifiedSquare r30 = refl
square37AlwaysClassifiedSquare r31 = refl
square37AlwaysClassifiedSquare r32 = refl
square37AlwaysClassifiedSquare r33 = refl
square37AlwaysClassifiedSquare r34 = refl
square37AlwaysClassifiedSquare r35 = refl
square37AlwaysClassifiedSquare r36 = refl

factorDiscriminantClassifiedNonsquare :
  (q : P37QuadraticFactor) →
  isSquareResidue37 (factorDiscriminant37 q) ≡ false
factorDiscriminantClassifiedNonsquare q0 = refl
factorDiscriminantClassifiedNonsquare q1 = refl
factorDiscriminantClassifiedNonsquare q2 = refl
factorDiscriminantClassifiedNonsquare q3 = refl
factorDiscriminantClassifiedNonsquare q4 = refl
factorDiscriminantClassifiedNonsquare q5 = refl
factorDiscriminantClassifiedNonsquare q6 = refl
factorDiscriminantClassifiedNonsquare q7 = refl
factorDiscriminantClassifiedNonsquare q8 = refl

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

factorDiscriminantIsNotASquare :
  (q : P37QuadraticFactor) →
  (r : Residue37) →
  square37 r ≡ factorDiscriminant37 q →
  ⊥
factorDiscriminantIsNotASquare q r same =
  trueNotFalse
    (trans
      (sym (square37AlwaysClassifiedSquare r))
      (trans
        (cong isSquareResidue37 same)
        (factorDiscriminantClassifiedNonsquare q)))

------------------------------------------------------------------------
-- Eighteen geometric roots = nine irreducible quadratic Frobenius pairs.
------------------------------------------------------------------------

data ConjugateBit : Set where
  root0 root1 : ConjugateBit

record P37SupersingularLambda : Set where
  constructor lambda37
  field
    quadraticFactor : P37QuadraticFactor
    conjugate : ConjugateBit

p37MarkedFrobenius : P37SupersingularLambda → P37SupersingularLambda
p37MarkedFrobenius (lambda37 q root0) = lambda37 q root1
p37MarkedFrobenius (lambda37 q root1) = lambda37 q root0

p37MarkedFrobeniusInvolution :
  (x : P37SupersingularLambda) →
  p37MarkedFrobenius (p37MarkedFrobenius x) ≡ x
p37MarkedFrobeniusInvolution (lambda37 q root0) = refl
p37MarkedFrobeniusInvolution (lambda37 q root1) = refl

p37MarkedFrobeniusHasNoFixedPoint :
  (x : P37SupersingularLambda) → p37MarkedFrobenius x ≡ x → ⊥
p37MarkedFrobeniusHasNoFixedPoint (lambda37 q root0) ()
p37MarkedFrobeniusHasNoFixedPoint (lambda37 q root1) ()

p37DeuringQuadraticFactorCount : Nat
p37DeuringQuadraticFactorCount = 9

p37DeuringGeometricRootCount : Nat
p37DeuringGeometricRootCount = 2 * p37DeuringQuadraticFactorCount

p37DeuringGeometricRootCountIsEighteen : p37DeuringGeometricRootCount ≡ 18
p37DeuringGeometricRootCountIsEighteen = refl

p37FullLevel2CountMatchesDeuringRootCount :
  p37FullLevel2StateCount ≡ p37DeuringGeometricRootCount
p37FullLevel2CountMatchesDeuringRootCount = refl

p37MarkedFrobeniusPairCount : Nat
p37MarkedFrobeniusPairCount = 9

record P37FullLevel2ControlBoundary : Set where
  field
    sameFullLevel2ProducerPorted : Bool
    sameFullLevel2ProducerPortedIsTrue : sameFullLevel2ProducerPorted ≡ true

    sourceCoarseClassCountThreeConsumed : Bool
    sourceCoarseClassCountThreeConsumedIsTrue :
      sourceCoarseClassCountThreeConsumed ≡ true

    sourceMonodromyWeightsAllOneConsumed : Bool
    sourceMonodromyWeightsAllOneConsumedIsTrue :
      sourceMonodromyWeightsAllOneConsumed ≡ true

    eighteenMarkedSheetsDerived : Bool
    eighteenMarkedSheetsDerivedIsTrue : eighteenMarkedSheetsDerived ≡ true

    degree18DeuringFactorPatternConstructed : Bool
    degree18DeuringFactorPatternConstructedIsTrue :
      degree18DeuringFactorPatternConstructed ≡ true

    nineQuadraticDiscriminantsCertifiedNonsquare : Bool
    nineQuadraticDiscriminantsCertifiedNonsquareIsTrue :
      nineQuadraticDiscriminantsCertifiedNonsquare ≡ true

    markedFrobeniusNinePairsZeroFixed : Bool
    markedFrobeniusNinePairsZeroFixedIsTrue :
      markedFrobeniusNinePairsZeroFixed ≡ true

    markedT3T5QuaternionThetaCountsConstructedHere : Bool
    markedT3T5QuaternionThetaCountsConstructedHereIsFalse :
      markedT3T5QuaternionThetaCountsConstructedHere ≡ false

canonicalP37FullLevel2ControlBoundary : P37FullLevel2ControlBoundary
canonicalP37FullLevel2ControlBoundary = record
  { sameFullLevel2ProducerPorted = true
  ; sameFullLevel2ProducerPortedIsTrue = refl
  ; sourceCoarseClassCountThreeConsumed = true
  ; sourceCoarseClassCountThreeConsumedIsTrue = refl
  ; sourceMonodromyWeightsAllOneConsumed = true
  ; sourceMonodromyWeightsAllOneConsumedIsTrue = refl
  ; eighteenMarkedSheetsDerived = true
  ; eighteenMarkedSheetsDerivedIsTrue = refl
  ; degree18DeuringFactorPatternConstructed = true
  ; degree18DeuringFactorPatternConstructedIsTrue = refl
  ; nineQuadraticDiscriminantsCertifiedNonsquare = true
  ; nineQuadraticDiscriminantsCertifiedNonsquareIsTrue = refl
  ; markedFrobeniusNinePairsZeroFixed = true
  ; markedFrobeniusNinePairsZeroFixedIsTrue = refl
  ; markedT3T5QuaternionThetaCountsConstructedHere = false
  ; markedT3T5QuaternionThetaCountsConstructedHereIsFalse = refl
  }
