module DASHI.Moonshine.P13LegendreJReductionCertificateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Josep Gonzalez,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300. DOI: 10.1016/j.jnt.2021.06.011.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Strengthen the p=13 finite-field control by making the final Legendre-j
-- reduction non-tautological at the integer congruence layer.  For each of the
-- three irreducible quadratic Deuring factors, the already-computed numerator
-- and denominator remainders N=a+bx and D=c+dx satisfy
--
--     N = 5 D  (mod 13)
--
-- coefficientwise.  The quotient multiples of 13 are recorded explicitly.
-- Thus the statement "all six marked lambda roots map to j=5" is backed by
-- integer congruence witnesses rather than by two definitionally equal lookup
-- tables.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P13OggFullLevel2DeuringControlExact as P13

------------------------------------------------------------------------
-- q0: N=(8,2), D=(12,3).
------------------------------------------------------------------------

q0ConstantJFiveCongruence : 5 * 12 ≡ 8 + 13 * 4
q0ConstantJFiveCongruence = refl

q0LinearJFiveCongruence : 5 * 3 ≡ 2 + 13 * 1
q0LinearJFiveCongruence = refl

------------------------------------------------------------------------
-- q1: N=(10,11), D=(2,10).
------------------------------------------------------------------------

q1ConstantJFiveCongruence : 5 * 2 ≡ 10 + 13 * 0
q1ConstantJFiveCongruence = refl

q1LinearJFiveCongruence : 5 * 10 ≡ 11 + 13 * 3
q1LinearJFiveCongruence = refl

------------------------------------------------------------------------
-- q2: N=(6,0), D=(9,0).
------------------------------------------------------------------------

q2ConstantJFiveCongruence : 5 * 9 ≡ 6 + 13 * 3
q2ConstantJFiveCongruence = refl

q2LinearJFiveCongruence : 5 * 0 ≡ 0 + 13 * 0
q2LinearJFiveCongruence = refl

------------------------------------------------------------------------
-- Package the six integer congruences by Deuring factor.
------------------------------------------------------------------------

record JFiveCoefficientCongruence : Set where
  field
    denominatorConstant denominatorLinear : Nat
    numeratorConstant numeratorLinear : Nat
    constantQuotient linearQuotient : Nat
    constantCongruence :
      5 * denominatorConstant
      ≡ numeratorConstant + 13 * constantQuotient
    linearCongruence :
      5 * denominatorLinear
      ≡ numeratorLinear + 13 * linearQuotient

open JFiveCoefficientCongruence public

jFiveCertificate : P13.P13QuadraticFactor → JFiveCoefficientCongruence
jFiveCertificate P13.q0 = record
  { denominatorConstant = 12
  ; denominatorLinear = 3
  ; numeratorConstant = 8
  ; numeratorLinear = 2
  ; constantQuotient = 4
  ; linearQuotient = 1
  ; constantCongruence = q0ConstantJFiveCongruence
  ; linearCongruence = q0LinearJFiveCongruence
  }
jFiveCertificate P13.q1 = record
  { denominatorConstant = 2
  ; denominatorLinear = 10
  ; numeratorConstant = 10
  ; numeratorLinear = 11
  ; constantQuotient = 0
  ; linearQuotient = 3
  ; constantCongruence = q1ConstantJFiveCongruence
  ; linearCongruence = q1LinearJFiveCongruence
  }
jFiveCertificate P13.q2 = record
  { denominatorConstant = 9
  ; denominatorLinear = 0
  ; numeratorConstant = 6
  ; numeratorLinear = 0
  ; constantQuotient = 3
  ; linearQuotient = 0
  ; constantCongruence = q2ConstantJFiveCongruence
  ; linearCongruence = q2LinearJFiveCongruence
  }

certificateMatchesStoredRemainders :
  (q : P13.P13QuadraticFactor) →
  P13.jDenominatorRemainder q
  ≡ P13.rem
      (denominatorConstant (jFiveCertificate q))
      (denominatorLinear (jFiveCertificate q))
certificateMatchesStoredRemainders P13.q0 = refl
certificateMatchesStoredRemainders P13.q1 = refl
certificateMatchesStoredRemainders P13.q2 = refl

certificateMatchesStoredNumerator :
  (q : P13.P13QuadraticFactor) →
  P13.jNumeratorRemainder q
  ≡ P13.rem
      (numeratorConstant (jFiveCertificate q))
      (numeratorLinear (jFiveCertificate q))
certificateMatchesStoredNumerator P13.q0 = refl
certificateMatchesStoredNumerator P13.q1 = refl
certificateMatchesStoredNumerator P13.q2 = refl

record P13LegendreJReductionBoundary : Set where
  field
    integerCongruenceCertificatesConstructed : Bool
    allThreeDeuringFactorsCovered : Bool
    coarseJValueFiveCertified : Bool
    finiteFieldDivisionByZeroSilentlyAssumed : Bool

canonicalP13LegendreJReductionBoundary : P13LegendreJReductionBoundary
canonicalP13LegendreJReductionBoundary = record
  { integerCongruenceCertificatesConstructed = true
  ; allThreeDeuringFactorsCovered = true
  ; coarseJValueFiveCertified = true
  ; finiteFieldDivisionByZeroSilentlyAssumed = false
  }
