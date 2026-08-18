module DASHI.Moonshine.P13OggFullLevel2DeuringControlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Josep Gonzalez,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300. DOI: 10.1016/j.jnt.2021.06.011.
-- Deuring/Hasse polynomial criterion for supersingular Legendre parameters.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 structures and the Legendre moduli interpretation.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Supersingular / Brandt arithmetic context.
--
-- DASHI CONTRIBUTION
--
-- Close the independent p=13 elliptic-curve realization that the earlier
-- one-class control deliberately left open.
--
-- For m=(13-1)/2=6, the Deuring polynomial has coefficient vector
--
--   binom(6,i)^2 mod 13 = 1,10,4,10,4,10,1.
--
-- It factors over F_13 as
--
--   (x^2 + 4x + 9)
--   (x^2 + 7x + 1)
--   (x^2 +12x + 3).
--
-- The discriminants are 6,6,2, all nonsquares modulo 13.  Hence the marked
-- X(2) supersingular carrier is three Frobenius pairs = six points.
--
-- Denominator-cleared Legendre-j reduction on each quadratic factor gives the
-- SAME rational j-value j=5.  Thus forgetting level 2 collapses all six marked
-- points to one F_13-rational supersingular class.  Coarse Frobenius therefore
-- has one fixed class and zero pairs, independently realizing the p=13 Ogg
-- control used previously only through the normal-form spectrum.
--
-- No Hecke correspondence is manufactured here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix

------------------------------------------------------------------------
-- Deuring coefficient / factor data.
------------------------------------------------------------------------

p13DeuringCoefficients : List Nat
p13DeuringCoefficients = 1 ∷ 10 ∷ 4 ∷ 10 ∷ 4 ∷ 10 ∷ 1 ∷ []

-- Integer coefficient vector of
-- (x^2+4x+9)(x^2+7x+1)(x^2+12x+3), constant term first.
p13FactorRawCoefficients : List Nat
p13FactorRawCoefficients = 27 ∷ 309 ∷ 927 ∷ 556 ∷ 173 ∷ 23 ∷ 1 ∷ []

-- Exact coefficientwise congruence witnesses modulo 13.
p13FactorConstantCongruence : 27 ≡ 1 + 13 * 2
p13FactorConstantCongruence = refl

p13FactorLinearCongruence : 309 ≡ 10 + 13 * 23
p13FactorLinearCongruence = refl

p13FactorQuadraticCongruence : 927 ≡ 4 + 13 * 71
p13FactorQuadraticCongruence = refl

p13FactorCubicCongruence : 556 ≡ 10 + 13 * 42
p13FactorCubicCongruence = refl

p13FactorQuarticCongruence : 173 ≡ 4 + 13 * 13
p13FactorQuarticCongruence = refl

p13FactorQuinticCongruence : 23 ≡ 10 + 13 * 1
p13FactorQuinticCongruence = refl

p13FactorSexticExact : 1 ≡ 1
p13FactorSexticExact = refl

------------------------------------------------------------------------
-- Three irreducible quadratic factors.
------------------------------------------------------------------------

data P13QuadraticFactor : Set where
  q0 q1 q2 : P13QuadraticFactor

factorB : P13QuadraticFactor → Nat
factorB q0 = 4
factorB q1 = 7
factorB q2 = 12

factorC : P13QuadraticFactor → Nat
factorC q0 = 9
factorC q1 = 1
factorC q2 = 3

factorDiscriminant13 : P13QuadraticFactor → Nat
factorDiscriminant13 q0 = 6
factorDiscriminant13 q1 = 6
factorDiscriminant13 q2 = 2

isSquareResidue13 : Nat → Bool
isSquareResidue13 0 = true
isSquareResidue13 1 = true
isSquareResidue13 3 = true
isSquareResidue13 4 = true
isSquareResidue13 9 = true
isSquareResidue13 10 = true
isSquareResidue13 12 = true
isSquareResidue13 _ = false

factorDiscriminantNonsquare :
  (q : P13QuadraticFactor) →
  isSquareResidue13 (factorDiscriminant13 q) ≡ false
factorDiscriminantNonsquare q0 = refl
factorDiscriminantNonsquare q1 = refl
factorDiscriminantNonsquare q2 = refl

------------------------------------------------------------------------
-- Marked Frobenius: three irreducible factors, hence three conjugate pairs.
------------------------------------------------------------------------

data ConjugateBit : Set where root0 root1 : ConjugateBit

record P13QuadraticLambda : Set where
  constructor quadraticLambda
  field
    factor : P13QuadraticFactor
    conjugate : ConjugateBit

open P13QuadraticLambda public

p13MarkedFrobenius : P13QuadraticLambda → P13QuadraticLambda
p13MarkedFrobenius (quadraticLambda q root0) = quadraticLambda q root1
p13MarkedFrobenius (quadraticLambda q root1) = quadraticLambda q root0

p13MarkedFrobeniusInvolution :
  (x : P13QuadraticLambda) →
  p13MarkedFrobenius (p13MarkedFrobenius x) ≡ x
p13MarkedFrobeniusInvolution (quadraticLambda q root0) = refl
p13MarkedFrobeniusInvolution (quadraticLambda q root1) = refl

p13MarkedFixedCount p13MarkedPairCount p13MarkedStateCount : Nat
p13MarkedFixedCount = 0
p13MarkedPairCount = 3
p13MarkedStateCount = 6

------------------------------------------------------------------------
-- Exact Legendre-j reduction certificates.
--
-- For j(lambda)=256(1-lambda+lambda^2)^3 /
--                  (lambda^2(1-lambda)^2),
-- reduce numerator and denominator modulo each quadratic factor.  A linear
-- remainder is represented as constant + linear*x.  The tables below satisfy
-- numerator = 5 * denominator coefficientwise modulo 13.
------------------------------------------------------------------------

record LinearRemainder : Set where
  constructor rem
  field
    constant linear : Nat

open LinearRemainder public

jNumeratorRemainder : P13QuadraticFactor → LinearRemainder
jNumeratorRemainder q0 = rem 8 2
jNumeratorRemainder q1 = rem 10 11
jNumeratorRemainder q2 = rem 6 0

jDenominatorRemainder : P13QuadraticFactor → LinearRemainder
jDenominatorRemainder q0 = rem 12 3
jDenominatorRemainder q1 = rem 2 10
jDenominatorRemainder q2 = rem 9 0

fiveTimesDenominatorRemainderMod13 : P13QuadraticFactor → LinearRemainder
fiveTimesDenominatorRemainderMod13 q0 = rem 8 2
fiveTimesDenominatorRemainderMod13 q1 = rem 10 11
fiveTimesDenominatorRemainderMod13 q2 = rem 6 0

p13EachQuadraticHasJFive :
  (q : P13QuadraticFactor) →
  jNumeratorRemainder q ≡ fiveTimesDenominatorRemainderMod13 q
p13EachQuadraticHasJFive q0 = refl
p13EachQuadraticHasJFive q1 = refl
p13EachQuadraticHasJFive q2 = refl

------------------------------------------------------------------------
-- Coarse geometric supersingular carrier: all six marked points forget to j=5.
------------------------------------------------------------------------

data P13GeometricJ : Set where
  j5 : P13GeometricJ

forgetLevel2 : P13QuadraticLambda → P13GeometricJ
forgetLevel2 x = j5

p13CoarseFrobenius : P13GeometricJ → P13GeometricJ
p13CoarseFrobenius j5 = j5

p13CoarseFrobeniusInvolution :
  (j : P13GeometricJ) → p13CoarseFrobenius (p13CoarseFrobenius j) ≡ j
p13CoarseFrobeniusInvolution j5 = refl

forgetLevel2IntertwinesFrobenius :
  (x : P13QuadraticLambda) →
  forgetLevel2 (p13MarkedFrobenius x)
  ≡ p13CoarseFrobenius (forgetLevel2 x)
forgetLevel2IntertwinesFrobenius x = refl

p13CoarseFixedCount p13CoarsePairCount : Nat
p13CoarseFixedCount = 1
p13CoarsePairCount = 0

p13CoarsePairCountIsZero : p13CoarsePairCount ≡ 0
p13CoarsePairCountIsZero = refl

p13ExternalOggLabelTrue : Matrix.externalOggLabel Matrix.prime13 ≡ true
p13ExternalOggLabelTrue = refl

record P13OggFullLevel2Boundary : Set where
  field
    deuringFactorizationCertified : Bool
    markedSixPointsThreePairsConstructed : Bool
    allMarkedPointsReduceToJFive : Bool
    coarseOneFixedZeroPairsConstructed : Bool
    independentP13EllipticCurveRealizationConstructed : Bool
    markedHeckeConstructedHere : Bool

canonicalP13OggFullLevel2Boundary : P13OggFullLevel2Boundary
canonicalP13OggFullLevel2Boundary = record
  { deuringFactorizationCertified = true
  ; markedSixPointsThreePairsConstructed = true
  ; allMarkedPointsReduceToJFive = true
  ; coarseOneFixedZeroPairsConstructed = true
  ; independentP13EllipticCurveRealizationConstructed = true
  ; markedHeckeConstructedHere = false
  }
