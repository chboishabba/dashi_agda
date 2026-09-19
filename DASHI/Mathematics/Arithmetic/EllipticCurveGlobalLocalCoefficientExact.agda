module DASHI.Mathematics.Arithmetic.EllipticCurveGlobalLocalCoefficientExact where

------------------------------------------------------------------------
-- GLOBAL PRIME-INDEXED LOCAL DATA FOR AN ELLIPTIC CURVE
--
-- This owner makes the finite BSD rows restrictions of one all-prime object.
-- Good and bad reduction are explicit, disjoint branches.  On good primes the
-- local Euler polynomial is
--
--   1 - a_p T + p T^2.
--
-- On bad primes this owner stores the supplied bad local polynomial rather
-- than silently applying the good-reduction formula.
--
-- Construction of the actual reduction classification and traces for every
-- rational elliptic curve remains domain arithmetic; modularity and the
-- infinite L-function remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Automorphic.TruncatedLFunctionExact as Truncated

data ReductionKind : Set where
  goodReduction : ReductionKind
  multiplicativeReduction : ReductionKind
  additiveReduction : ReductionKind

record PrimeLocalDatum
    (curve : Elliptic.ShortWeierstrassCurve) : Set₁ where
  field
    primeLabel : Nat
    primeAsRational : ℚ
    reductionKind : ReductionKind
    frobeniusCoefficient : ℚ

    constantCoefficient : ℚ
    linearCoefficient : ℚ
    quadraticCoefficient : ℚ

    constantIsOne : constantCoefficient ≡ 1ℚ

    goodLinearMeaning :
      reductionKind ≡ goodReduction →
      linearCoefficient ≡ - frobeniusCoefficient
    goodQuadraticMeaning :
      reductionKind ≡ goodReduction →
      quadraticCoefficient ≡ primeAsRational

    badQuadraticVanishes :
      reductionKind ≡ multiplicativeReduction →
      quadraticCoefficient ≡ 0ℚ
    additiveQuadraticVanishes :
      reductionKind ≡ additiveReduction →
      quadraticCoefficient ≡ 0ℚ

open PrimeLocalDatum public

localPolynomialValue :
  ∀ {curve} →
  PrimeLocalDatum curve → ℚ → ℚ
localPolynomialValue datum T =
  constantCoefficient datum
  + linearCoefficient datum * T
  + quadraticCoefficient datum * T * T

record EllipticCurveGlobalLocalCoefficient
    (curve : Elliptic.ShortWeierstrassCurve) : Set₁ where
  field
    localAtPrime : Nat → PrimeLocalDatum curve
    primeLabelExact :
      (p : Nat) → primeLabel (localAtPrime p) ≡ p

open EllipticCurveGlobalLocalCoefficient public

GoodPrime :
  ∀ {curve} →
  EllipticCurveGlobalLocalCoefficient curve →
  Nat → Set
GoodPrime family p =
  reductionKind (localAtPrime family p) ≡ goodReduction

primeNormFromGlobal :
  ∀ {curve}
    (family : EllipticCurveGlobalLocalCoefficient curve) →
  Nat → Truncated.PrimeNorm
primeNormFromGlobal family p =
  Truncated.primeNorm
    p
    (primeAsRational (localAtPrime family p))

goodPrimeCoefficientData :
  ∀ {curve}
    (family : EllipticCurveGlobalLocalCoefficient curve) →
  Truncated.LocalCoefficientData
goodPrimeCoefficientData family = record
  { Truncated.coefficient =
      λ prime →
        frobeniusCoefficient
          (localAtPrime family
            (Truncated.primeLabel prime))
  }

goodPrimeLocalFactorIsGlobalPolynomial :
  ∀ {curve}
    (family : EllipticCurveGlobalLocalCoefficient curve)
    (p : Nat) →
  GoodPrime family p →
  ∀ T →
  Truncated.localEulerFactorValue
    (goodPrimeCoefficientData family)
    (primeNormFromGlobal family p)
    T
  ≡ localPolynomialValue (localAtPrime family p) T
goodPrimeLocalFactorIsGlobalPolynomial family p good T
    with constantIsOne (localAtPrime family p)
       | goodLinearMeaning (localAtPrime family p) good
       | goodQuadraticMeaning (localAtPrime family p) good
... | refl | refl | refl = refl

record FiniteGoodPrimeRestriction
    {curve : Elliptic.ShortWeierstrassCurve}
    (family : EllipticCurveGlobalLocalCoefficient curve)
    (p : Nat) : Set where
  field
    good : GoodPrime family p

open FiniteGoodPrimeRestriction public

restrictedPrimeNorm :
  ∀ {curve family p} →
  FiniteGoodPrimeRestriction {curve = curve} family p →
  Truncated.PrimeNorm
restrictedPrimeNorm {family = family} {p = p} restriction =
  primeNormFromGlobal family p

restrictedCoefficientIsGlobal :
  ∀ {curve family p}
    (restriction : FiniteGoodPrimeRestriction {curve = curve} family p) →
  Truncated.coefficient
    (goodPrimeCoefficientData family)
    (restrictedPrimeNorm restriction)
  ≡ frobeniusCoefficient (localAtPrime family p)
restrictedCoefficientIsGlobal restriction = refl

restrictedLocalFactorIsGlobal :
  ∀ {curve family p}
    (restriction : FiniteGoodPrimeRestriction {curve = curve} family p)
    T →
  Truncated.localEulerFactorValue
    (goodPrimeCoefficientData family)
    (restrictedPrimeNorm restriction)
    T
  ≡ localPolynomialValue (localAtPrime family p) T
restrictedLocalFactorIsGlobal {family = family} {p = p} restriction T =
  goodPrimeLocalFactorIsGlobalPolynomial
    family p (good restriction) T
