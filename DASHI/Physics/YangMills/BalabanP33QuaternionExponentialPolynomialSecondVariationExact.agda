module DASHI.Physics.YangMills.BalabanP33QuaternionExponentialPolynomialSecondVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Joseph Diestel and John J. Uhl, Jr.,
-- "Vector Measures", Mathematical Surveys 15, American Mathematical Society,
-- 1977. DOI: 10.1090/SURV/015.
--
-- Jan Mikusinski,
-- "The Bochner Integral", Birkhaeuser, 1978.
-- DOI: 10.1007/978-3-0348-5567-9.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact finite power-series identity underlying the physical
-- Bochner-integral Duhamel formula.  For the affine two-parameter perturbation
--
--   X(t,s) = X + t H + s K,
--
-- the mixed coefficient of X(t,s)^n is the sum of all words containing one H
-- and one K, in both possible orders.  The recursion is
--
--   D_H(X^(n+1)) = D_H(X^n) X + X^n H,
--
--   D_HK(X^(n+1))
--     = D_HK(X^n) X + D_H(X^n) K + D_K(X^n) H.
--
-- Separately, the ordered insertion sums satisfy precisely the same recursion:
--
--   W_HK(n+1) = W_HK(n) X + D_H(X^n) K,
--   W_KH(n+1) = W_KH(n) X + D_K(X^n) H.
--
-- Hence, for every truncation N,
--
--   D^2 [sum_{n=0}^N X^n/n!] [H,K]
--     = sum_{n=0}^N (W_HK(n)+W_KH(n))/n!.
--
-- This is the exact algebraic series form of the two ordered-simplex Duhamel
-- integrals.  The only remaining analytic step is to identify the convergent
-- limit with the Bochner integrals and justify differentiation under that
-- limit.  No noncommutative rearrangement is left implicit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _/_)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (Quaternion; zeroQ; oneQ; _+q_; _*q_; scaleRealQ)

------------------------------------------------------------------------
-- Powers and first insertion sums.
------------------------------------------------------------------------

quaternionPower : Quaternion → Nat → Quaternion
quaternionPower x zero = oneQ
quaternionPower x (suc n) = quaternionPower x n *q x

firstInsertion : Quaternion → Quaternion → Nat → Quaternion
firstInsertion x h zero = zeroQ
firstInsertion x h (suc n) =
  (firstInsertion x h n *q x)
  +q (quaternionPower x n *q h)

------------------------------------------------------------------------
-- Mixed derivative recursion and the two ordered word families.
------------------------------------------------------------------------

mixedPowerVariation :
  Quaternion → Quaternion → Quaternion → Nat → Quaternion
mixedPowerVariation x h k zero = zeroQ
mixedPowerVariation x h k (suc n) =
  (mixedPowerVariation x h k n *q x)
  +q ((firstInsertion x h n *q k)
    +q (firstInsertion x k n *q h))

orderedHKWords :
  Quaternion → Quaternion → Quaternion → Nat → Quaternion
orderedHKWords x h k zero = zeroQ
orderedHKWords x h k (suc n) =
  (orderedHKWords x h k n *q x)
  +q (firstInsertion x h n *q k)

orderedKHWords :
  Quaternion → Quaternion → Quaternion → Nat → Quaternion
orderedKHWords x h k zero = zeroQ
orderedKHWords x h k (suc n) =
  (orderedKHWords x h k n *q x)
  +q (firstInsertion x k n *q h)

orderedSecondInsertionWords :
  Quaternion → Quaternion → Quaternion → Nat → Quaternion
orderedSecondInsertionWords x h k n =
  orderedHKWords x h k n +q orderedKHWords x h k n

mixedPowerVariationIsOrderedWords :
  ∀ x h k n →
  mixedPowerVariation x h k n
  ≡ orderedSecondInsertionWords x h k n
mixedPowerVariationIsOrderedWords x h k zero = refl
mixedPowerVariationIsOrderedWords x h k (suc n)
  rewrite mixedPowerVariationIsOrderedWords x h k n = refl

------------------------------------------------------------------------
-- Recursive factorial coefficients, represented without a partial division.
--
--   c_0 = 1,
--   c_(n+1) = c_n/(n+1).
------------------------------------------------------------------------

factorialCoefficient : Nat → ℚ
factorialCoefficient zero = 1ℚ
factorialCoefficient (suc n) =
  factorialCoefficient n * (+ 1 / suc n)

weightedMixedPower :
  Quaternion → Quaternion → Quaternion → Nat → Quaternion
weightedMixedPower x h k n =
  scaleRealQ (factorialCoefficient n)
    (mixedPowerVariation x h k n)

weightedOrderedWords :
  Quaternion → Quaternion → Quaternion → Nat → Quaternion
weightedOrderedWords x h k n =
  scaleRealQ (factorialCoefficient n)
    (orderedSecondInsertionWords x h k n)

weightedMixedPowerIsOrderedWords :
  ∀ x h k n →
  weightedMixedPower x h k n
  ≡ weightedOrderedWords x h k n
weightedMixedPowerIsOrderedWords x h k n =
  congruence
  where
    congruence =
      Relation.Binary.PropositionalEquality.cong
        (scaleRealQ (factorialCoefficient n))
        (mixedPowerVariationIsOrderedWords x h k n)

------------------------------------------------------------------------
-- Truncated exponential second variation and truncated Duhamel word series.
------------------------------------------------------------------------

truncatedExponentialSecondVariation :
  Nat → Quaternion → Quaternion → Quaternion → Quaternion
truncatedExponentialSecondVariation zero x h k =
  weightedMixedPower x h k zero
truncatedExponentialSecondVariation (suc n) x h k =
  truncatedExponentialSecondVariation n x h k
  +q weightedMixedPower x h k (suc n)

truncatedDuhamelWordSeries :
  Nat → Quaternion → Quaternion → Quaternion → Quaternion
truncatedDuhamelWordSeries zero x h k =
  weightedOrderedWords x h k zero
truncatedDuhamelWordSeries (suc n) x h k =
  truncatedDuhamelWordSeries n x h k
  +q weightedOrderedWords x h k (suc n)

truncatedExponentialSecondVariationIsDuhamelWords :
  ∀ cutoff x h k →
  truncatedExponentialSecondVariation cutoff x h k
  ≡ truncatedDuhamelWordSeries cutoff x h k
truncatedExponentialSecondVariationIsDuhamelWords zero x h k =
  weightedMixedPowerIsOrderedWords x h k zero
truncatedExponentialSecondVariationIsDuhamelWords (suc cutoff) x h k =
  cong₂ _+q_
    (truncatedExponentialSecondVariationIsDuhamelWords cutoff x h k)
    (weightedMixedPowerIsOrderedWords x h k (suc cutoff))

------------------------------------------------------------------------
-- The zero-background value is already the expected symmetrised product.
------------------------------------------------------------------------

factorialCoefficientTwo :
  factorialCoefficient (suc (suc zero)) ≡ (+ 1 / 2)
factorialCoefficientTwo = refl

mixedPowerTwo : ∀ x h k →
  mixedPowerVariation x h k (suc (suc zero))
  ≡ (h *q k) +q (k *q h)
mixedPowerTwo x h k = refl

quaternionExponentialPolynomialSecondVariationLevel : ProofLevel
quaternionExponentialPolynomialSecondVariationLevel = machineChecked

quaternionDuhamelWordReindexingLevel : ProofLevel
quaternionDuhamelWordReindexingLevel = machineChecked

bochnerLimitAndDifferentiationProducerLevel : ProofLevel
bochnerLimitAndDifferentiationProducerLevel = conditional
