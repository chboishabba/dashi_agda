module DASHI.Moonshine.RankOneFockEulerProductPrefixExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Victor G. Kac,
-- "Vertex Algebras for Beginners", second edition.
-- No DOI is asserted for the cited AMS book edition.
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "A natural representation of the Fischer-Griess Monster with the modular
-- function J as character",
-- Proceedings of the National Academy of Sciences 81 (1984), 3256--3260.
-- DOI: 10.1073/pnas.81.10.3256.
--
-- DASHI CONTRIBUTION
--
-- Derive the exact rank-one Fock character prefix from the truncated Euler
-- product
--
--   product_{n=1}^5 (1-q^n)^(-1) mod q^6.
--
-- Each local factor is expanded only through degree five; exact truncated
-- convolution gives coefficients 1,1,2,3,5,7, matching the independently
-- constructed oscillator partition basis in grades zero through five.
-- Infinite products and Dedekind-eta modularity remain separate boundaries.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Moonshine.RankOneFockPartitionGradingExact as Fock

record PolynomialDegreeFive : Set where
  constructor polynomial6
  field
    coefficient0 coefficient1 coefficient2
      coefficient3 coefficient4 coefficient5 : Nat

open PolynomialDegreeFive public

coefficients : PolynomialDegreeFive → List Nat
coefficients polynomial =
  coefficient0 polynomial
  ∷ coefficient1 polynomial
  ∷ coefficient2 polynomial
  ∷ coefficient3 polynomial
  ∷ coefficient4 polynomial
  ∷ coefficient5 polynomial
  ∷ []

multiplyTruncated :
  PolynomialDegreeFive → PolynomialDegreeFive → PolynomialDegreeFive
multiplyTruncated
    (polynomial6 a0 a1 a2 a3 a4 a5)
    (polynomial6 b0 b1 b2 b3 b4 b5) =
  polynomial6
    (a0 * b0)
    (a0 * b1 + a1 * b0)
    (a0 * b2 + a1 * b1 + a2 * b0)
    (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
    (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)
    (a0 * b5 + a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 + a5 * b0)

factorOne : PolynomialDegreeFive
factorOne = polynomial6 1 1 1 1 1 1

factorTwo : PolynomialDegreeFive
factorTwo = polynomial6 1 0 1 0 1 0

factorThree : PolynomialDegreeFive
factorThree = polynomial6 1 0 0 1 0 0

factorFour : PolynomialDegreeFive
factorFour = polynomial6 1 0 0 0 1 0

factorFive : PolynomialDegreeFive
factorFive = polynomial6 1 0 0 0 0 1

productThroughTwo : PolynomialDegreeFive
productThroughTwo = multiplyTruncated factorOne factorTwo

productThroughThree : PolynomialDegreeFive
productThroughThree = multiplyTruncated productThroughTwo factorThree

productThroughFour : PolynomialDegreeFive
productThroughFour = multiplyTruncated productThroughThree factorFour

productThroughFive : PolynomialDegreeFive
productThroughFive = multiplyTruncated productThroughFour factorFive

productThroughTwoCoefficients :
  coefficients productThroughTwo ≡ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ []
productThroughTwoCoefficients = refl

productThroughThreeCoefficients :
  coefficients productThroughThree ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
productThroughThreeCoefficients = refl

productThroughFourCoefficients :
  coefficients productThroughFour ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 6 ∷ []
productThroughFourCoefficients = refl

productThroughFiveCoefficients :
  coefficients productThroughFive ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 7 ∷ []
productThroughFiveCoefficients = refl

fockPrefixEqualsEulerProductPrefix :
  Fock.fockCharacterPrefix ≡ coefficients productThroughFive
fockPrefixEqualsEulerProductPrefix = refl

record FockEulerPrefixCertificate : Set where
  field
    throughTwo :
      coefficients productThroughTwo ≡ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ []
    throughThree :
      coefficients productThroughThree ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
    throughFour :
      coefficients productThroughFour ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 6 ∷ []
    throughFive :
      coefficients productThroughFive ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 7 ∷ []
    matchesFockBasis :
      Fock.fockCharacterPrefix ≡ coefficients productThroughFive

canonicalFockEulerPrefixCertificate : FockEulerPrefixCertificate
canonicalFockEulerPrefixCertificate = record
  { throughTwo = productThroughTwoCoefficients
  ; throughThree = productThroughThreeCoefficients
  ; throughFour = productThroughFourCoefficients
  ; throughFive = productThroughFiveCoefficients
  ; matchesFockBasis = fockPrefixEqualsEulerProductPrefix
  }

record InfiniteFockEtaBoundary : Set₁ where
  field
    formalInfiniteProduct : Set
    coefficientStabilisation : Set
    completedFockSpace : Set
    characterConvergence : Set
    etaProductIdentification : Set
    etaModularTransformation : Set
    VOACharacterModularity : Set
