{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopMachinOriginalCayleyFormalSeriesExact where

------------------------------------------------------------------------
-- K05-PI: ALL-DEGREE FORMAL CAYLEY PHASE ON THE ORIGINAL Q[i] CARRIER
--
-- Reuses the existing literal RationalComplex and complex operations from
-- CayleyDicksonRationalComplexQuaternionExact. In the polynomial coefficient
-- ring Q[i], the Cayley series
--
--     F(X) = (1 + iX)/(1 - iX)
--          = 1 + 2iX + 2i²X² + 2i³X³ + ...
--
-- has the unique recurrence
--
--     a₀ = 1, a₁ = 2i, a_(n+2) = i*a_(n+1).
--
-- The coefficient of (1-iX)F(X) at degree 0 is 1,
-- at degree 1 is i, and at every higher degree is 0.
--
-- This file supplies the *universal finite algebra* required for the
-- Bishop analytic atan/exp-to-Cayley weld. It is NOT that analytic weld:
-- identifying exp_C(2i atan_B(t)) with the evaluation of this formal
-- series requires the genuine source Bishop composition/limit theorem.
-- No new analytic functions, postulates, complex carrier or pi source.
--
-- Reused actual rational complex owner:
--   Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact.
-- Bishop analytic application:
--   Foundations.BishopMachinArctanConstructionExact.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _/_)
import Data.Rational.Tactic.RingSolver as RationalRing

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD

imaginaryUnit : CD.RationalComplex
imaginaryUnit = CD.complex 0ℚ 1ℚ

twoImaginaryUnits : CD.RationalComplex
twoImaginaryUnits = CD.complex 0ℚ (+ 2 / 1)

-- Coefficients of the ORIGINAL rational Gaussian Cayley transform.
cayleyFormalCoefficient : Nat → CD.RationalComplex
cayleyFormalCoefficient zero = CD.oneC
cayleyFormalCoefficient (suc zero) = twoImaginaryUnits
cayleyFormalCoefficient (suc (suc n)) =
  CD._*c_ imaginaryUnit (cayleyFormalCoefficient (suc n))

-- Denominator-times-series coefficient, with the shifted index exact.
-- This is a direct finite coefficient definition (no infinite sums).
cayleyDenominatorProductCoefficient : Nat → CD.RationalComplex
cayleyDenominatorProductCoefficient zero =
  cayleyFormalCoefficient zero
cayleyDenominatorProductCoefficient (suc n) =
  CD._-c_
    (cayleyFormalCoefficient (suc n))
    (CD._*c_ imaginaryUnit (cayleyFormalCoefficient n))

-- In the ORIGINAL rational complex ring, z - z = 0.
originalComplexSubtractSelf :
  (z : CD.RationalComplex) →
  CD._-c_ z z ≡ CD.zeroC
originalComplexSubtractSelf (CD.complex a b) =
  CD.complexExt
    RationalRing.solve-∀
    RationalRing.solve-∀

cayleyConstantCoefficient :
  cayleyDenominatorProductCoefficient zero ≡ CD.oneC
cayleyConstantCoefficient = refl

cayleyLinearCoefficient :
  cayleyDenominatorProductCoefficient (suc zero)
  ≡ imaginaryUnit
cayleyLinearCoefficient =
  CD.complexExt
    RationalRing.solve-∀
    RationalRing.solve-∀

cayleyAllHigherCoefficientsZero :
  (n : Nat) →
  cayleyDenominatorProductCoefficient (suc (suc n))
  ≡ CD.zeroC
cayleyAllHigherCoefficientsZero n =
  originalComplexSubtractSelf
    (CD._*c_ imaginaryUnit (cayleyFormalCoefficient (suc n)))

-- This is the untruncated, all-degree rational polynomial identity
--   (1-iX)F(X) = 1+iX,
-- expressed literally coefficient by coefficient.
cayleyFormalNumeratorCoefficient : Nat → CD.RationalComplex
cayleyFormalNumeratorCoefficient zero = CD.oneC
cayleyFormalNumeratorCoefficient (suc zero) = imaginaryUnit
cayleyFormalNumeratorCoefficient (suc (suc n)) = CD.zeroC

cayleyAllDegreeFormalEquation :
  (n : Nat) →
  cayleyDenominatorProductCoefficient n
  ≡ cayleyFormalNumeratorCoefficient n
cayleyAllDegreeFormalEquation zero = cayleyConstantCoefficient
cayleyAllDegreeFormalEquation (suc zero) =
  cayleyLinearCoefficient
cayleyAllDegreeFormalEquation (suc (suc n)) =
  cayleyAllHigherCoefficientsZero n

-- Formal uniqueness is also all-degree, not a rational regression.
-- Requiring the exact recurrence rules out any alternative coefficient
-- stream with an unannounced change to the Cayley normalization.
record OriginalCayleyFormalRecurrence
    (coefficient : Nat → CD.RationalComplex) : Set where
  field
    firstCoefficient :
      coefficient zero ≡ CD.oneC
    secondCoefficient :
      coefficient (suc zero) ≡ twoImaginaryUnits
    successorCoefficient :
      (n : Nat) →
      coefficient (suc (suc n))
      ≡ CD._*c_ imaginaryUnit (coefficient (suc n))

open OriginalCayleyFormalRecurrence public

canonicalCayleyFormalRecurrence :
  OriginalCayleyFormalRecurrence cayleyFormalCoefficient
canonicalCayleyFormalRecurrence = record
  { firstCoefficient = refl
  ; secondCoefficient = refl
  ; successorCoefficient = λ _ → refl
  }

originalCayleyFormalCoefficientUnique :
  (coefficient : Nat → CD.RationalComplex) →
  OriginalCayleyFormalRecurrence coefficient →
  (n : Nat) →
  coefficient n ≡ cayleyFormalCoefficient n
originalCayleyFormalCoefficientUnique coefficient eq zero =
  firstCoefficient eq
originalCayleyFormalCoefficientUnique coefficient eq (suc zero) =
  secondCoefficient eq
originalCayleyFormalCoefficientUnique coefficient eq (suc (suc n)) =
  trans
    (successorCoefficient eq n)
    (cong
      (CD._*c_ imaginaryUnit)
      (originalCayleyFormalCoefficientUnique
        coefficient eq (suc n)))
