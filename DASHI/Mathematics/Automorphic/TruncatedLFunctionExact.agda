module DASHI.Mathematics.Automorphic.TruncatedLFunctionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Toshitsune Miyake,
-- "Modular Forms".
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Construct rational local Euler factors
--
--   P_p(T) = 1 - a_p T + p T^2
--
-- and their finite products.  Product extension is definitional, while a
-- pointwise equality of elliptic Frobenius coefficients and modular Fourier
-- coefficients proves equality of every corresponding local factor and hence
-- equality of every truncated Euler product.
--
-- The theorem is deliberately finite.  Modularity, convergence, analytic
-- continuation and the infinite Euler product remain separate obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.NumberTheory.FiniteEulerProductExact as Euler
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as E5

------------------------------------------------------------------------
-- Rational semiring instance.
------------------------------------------------------------------------

rationalSemiring : Euler.CommutativeSemiring
rationalSemiring = record
  { Carrier = ℚ
  ; zero = 0ℚ
  ; one = 1ℚ
  ; add = _+_
  ; multiply = _*_
  ; addAssociative = λ x y z → solve (x ∷ y ∷ z ∷ [])
  ; addCommutative = λ x y → solve (x ∷ y ∷ [])
  ; addIdentityLeft = λ x → solve (x ∷ [])
  ; addIdentityRight = λ x → solve (x ∷ [])
  ; multiplyAssociative = λ x y z → solve (x ∷ y ∷ z ∷ [])
  ; multiplyCommutative = λ x y → solve (x ∷ y ∷ [])
  ; multiplyIdentityLeft = λ x → solve (x ∷ [])
  ; multiplyIdentityRight = λ x → solve (x ∷ [])
  ; multiplyZeroLeft = λ x → solve (x ∷ [])
  ; multiplyZeroRight = λ x → solve (x ∷ [])
  ; distributeLeft = λ x y z → solve (x ∷ y ∷ z ∷ [])
  ; distributeRight = λ x y z → solve (x ∷ y ∷ z ∷ [])
  }

record PrimeNorm : Set where
  constructor primeNorm
  field
    primeLabel : Nat
    primeAsRational : ℚ

open PrimeNorm public

record LocalCoefficientData : Set₁ where
  field
    coefficient : PrimeNorm → ℚ

open LocalCoefficientData public

localEulerFactorValue :
  LocalCoefficientData → PrimeNorm → ℚ → ℚ
localEulerFactorValue data prime T =
  1ℚ - coefficient data prime * T
    + primeAsRational prime * T * T

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

truncatedEulerDenominator :
  LocalCoefficientData → ℚ → List PrimeNorm → ℚ
truncatedEulerDenominator data T primes =
  Euler.productList rationalSemiring
    (mapList (λ prime → localEulerFactorValue data prime T) primes)

truncatedEulerDenominatorEmpty : ∀ data T →
  truncatedEulerDenominator data T [] ≡ 1ℚ
truncatedEulerDenominatorEmpty data T = refl

truncatedEulerDenominatorExtend : ∀ data T prime primes →
  truncatedEulerDenominator data T (prime ∷ primes)
  ≡ localEulerFactorValue data prime T
    * truncatedEulerDenominator data T primes
truncatedEulerDenominatorExtend data T prime primes = refl

record CoefficientAgreement
    (first second : LocalCoefficientData) : Set₁ where
  field
    coefficientsAgree : ∀ prime →
      coefficient first prime ≡ coefficient second prime

open CoefficientAgreement public

localFactorAgreement :
  ∀ {first second} → CoefficientAgreement first second →
  ∀ prime T →
  localEulerFactorValue first prime T
  ≡ localEulerFactorValue second prime T
localFactorAgreement agreement prime T
    with coefficientsAgree agreement prime
... | refl = refl

productOfPointwiseEqualLists :
  ∀ first second →
  (∀ index → Set) → Set
productOfPointwiseEqualLists first second witness = Set

truncatedEulerProductsAgree :
  ∀ {first second} → CoefficientAgreement first second →
  ∀ T primes →
  truncatedEulerDenominator first T primes
  ≡ truncatedEulerDenominator second T primes
truncatedEulerProductsAgree agreement T [] = refl
truncatedEulerProductsAgree agreement T (prime ∷ primes) =
  multiplyCongruence
    (localFactorAgreement agreement prime T)
    (truncatedEulerProductsAgree agreement T primes)
  where
    multiplyCongruence : ∀ {a a' b b' : ℚ} →
      a ≡ a' → b ≡ b' → a * b ≡ a' * b'
    multiplyCongruence refl refl = refl

------------------------------------------------------------------------
-- Elliptic/modular coefficient bridge.
------------------------------------------------------------------------

record EllipticCurveLocalData : Set₁ where
  field
    ellipticCoefficients : LocalCoefficientData
    frobeniusTraceMeaning : Set
    goodReductionPrimes : PrimeNorm → Set

record ModularFormFourierData : Set₁ where
  field
    modularCoefficients : LocalCoefficientData
    weightTwo : Set
    heckeEigenform : Set

record EllipticModularCoefficientAgreement
    (elliptic : EllipticCurveLocalData)
    (modular : ModularFormFourierData) : Set₁ where
  field
    coefficientAgreement :
      CoefficientAgreement
        (EllipticCurveLocalData.ellipticCoefficients elliptic)
        (ModularFormFourierData.modularCoefficients modular)

open EllipticModularCoefficientAgreement public

coefficientAgreementGivesTruncatedEulerAgreement :
  ∀ elliptic modular →
  EllipticModularCoefficientAgreement elliptic modular →
  ∀ T primes →
  truncatedEulerDenominator
    (EllipticCurveLocalData.ellipticCoefficients elliptic) T primes
  ≡ truncatedEulerDenominator
    (ModularFormFourierData.modularCoefficients modular) T primes
coefficientAgreementGivesTruncatedEulerAgreement
    elliptic modular agreement T primes =
  truncatedEulerProductsAgree
    (coefficientAgreement agreement) T primes

------------------------------------------------------------------------
-- Concrete p=5 reuse from the BSD seed.
------------------------------------------------------------------------

data P5Prime : Set where
  p5 : P5Prime

p5Norm : PrimeNorm
p5Norm = primeNorm 5 (1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ)

p5EllipticLocalCoefficients : LocalCoefficientData
p5EllipticLocalCoefficients = record
  { coefficient = λ prime → E5.frobeniusTraceAtFive }

p5ModularCandidateCoefficients : LocalCoefficientData
p5ModularCandidateCoefficients = record
  { coefficient = λ prime → E5.frobeniusTraceAtFive }

p5CoefficientAgreement :
  CoefficientAgreement
    p5EllipticLocalCoefficients p5ModularCandidateCoefficients
p5CoefficientAgreement = record
  { coefficientsAgree = λ prime → refl }

p5LocalFactorAgreement : ∀ T →
  localEulerFactorValue p5EllipticLocalCoefficients p5Norm T
  ≡ localEulerFactorValue p5ModularCandidateCoefficients p5Norm T
p5LocalFactorAgreement T = localFactorAgreement p5CoefficientAgreement p5Norm T

p5LocalFactorHasExpectedPolynomial : ∀ T →
  localEulerFactorValue p5EllipticLocalCoefficients p5Norm T
  ≡ 1ℚ + (1ℚ + 1ℚ) * T
      + (1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ) * T * T
p5LocalFactorHasExpectedPolynomial T =
  solve (T ∷ [])
