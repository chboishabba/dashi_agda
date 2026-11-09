{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopMachinCayleyEquationForcesCoefficientsExact where

------------------------------------------------------------------------
-- K05-PI P1.01: the ORIGINAL all-degree denominator equation
-- FORCES the unique Cayley coefficient sequence.
--
-- Earlier source requires a separately supplied recurrence. Here an
-- arbitrary Q[i] coefficient family satisfying (1-iX)F=1+iX at
-- EVERY finite degree is proved to satisfy that recurrence, and
-- therefore is pointwise the existing canonical Cayley coefficient.
-- Pure finite algebra. It does NOT assert the analytic exp(atan)
-- series obeys this equation; that remains the genuine P1 weld.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; trans; sym)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Foundations.BishopMachinOriginalCayleyFormalSeriesExact as Formal

-- The literal coefficient equation for an arbitrary family.
denominatorCoefficient :
  (c : Nat → CD.RationalComplex) → Nat → CD.RationalComplex
denominatorCoefficient c zero = c zero
denominatorCoefficient c (suc n) =
  CD._-c_ (c (suc n))
    (CD._*c_ Formal.imaginaryUnit (c n))

record SatisfiesOriginalCayleyEquation
    (c : Nat → CD.RationalComplex) : Set where
  field
    coefficientEquation :
      (n : Nat) →
      denominatorCoefficient c n
      ≡ Formal.cayleyFormalNumeratorCoefficient n
open SatisfiesOriginalCayleyEquation public

complexSubtractAddRight :
  (a b : CD.RationalComplex) →
  CD._+c_ (CD._-c_ a b) b ≡ a
complexSubtractAddRight (CD.complex a b) (CD.complex c d) =
  CD.complexExt
    (Ring.solve-∀)
    (Ring.solve-∀)

complexZeroAddLeft :
  (a : CD.RationalComplex) →
  CD._+c_ CD.zeroC a ≡ a
complexZeroAddLeft (CD.complex a b) =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

complexSubtractZeroForcesEquality :
  (a b : CD.RationalComplex) →
  CD._-c_ a b ≡ CD.zeroC → a ≡ b
complexSubtractZeroForcesEquality a b eq =
  trans
    (sym (complexSubtractAddRight a b))
    (trans
      (cong (λ z → CD._+c_ z b) eq)
      (complexZeroAddLeft b))

complexImaginaryUnitTimesOne :
  CD._*c_ Formal.imaginaryUnit CD.oneC
  ≡ Formal.imaginaryUnit
complexImaginaryUnitTimesOne =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

complexImaginaryUnitPlusSelf :
  CD._+c_ Formal.imaginaryUnit Formal.imaginaryUnit
  ≡ Formal.twoImaginaryUnits
complexImaginaryUnitPlusSelf =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

originalEquationForcesRecurrence :
  (c : Nat → CD.RationalComplex) →
  SatisfiesOriginalCayleyEquation c →
  Formal.OriginalCayleyFormalRecurrence c
originalEquationForcesRecurrence c equation = record
  { firstCoefficient = coefficientEquation equation zero
  ; secondCoefficient =
      let
        eq0 = coefficientEquation equation zero
        eq1 = coefficientEquation equation (suc zero)
        productCong =
          cong (CD._*c_ Formal.imaginaryUnit) eq0
        -- Replace the first coefficient by the proved unit.
        subtractCong :
          CD._-c_ (c (suc zero))
            (CD._*c_ Formal.imaginaryUnit (c zero))
          ≡
          CD._-c_ (c (suc zero)) Formal.imaginaryUnit
        subtractCong =
          cong (CD._-c_ (c (suc zero)))
            (trans productCong complexImaginaryUnitTimesOne)
        sameDifference :
          CD._-c_ (c (suc zero)) Formal.imaginaryUnit
          ≡ Formal.imaginaryUnit
        sameDifference = trans (sym subtractCong) eq1
      in
      trans
        (sym (complexSubtractAddRight
          (c (suc zero)) Formal.imaginaryUnit))
        (trans
          (cong (λ z → CD._+c_ z Formal.imaginaryUnit)
            sameDifference)
          complexImaginaryUnitPlusSelf)
  ; successorCoefficient = λ n →
      complexSubtractZeroForcesEquality
        (c (suc (suc n)))
        (CD._*c_ Formal.imaginaryUnit (c (suc n)))
        (coefficientEquation equation (suc (suc n)))
  }

-- Strengthening P1.01: the formal equation ALONE forces every
-- coefficient to equal the original rational Cayley series.
originalCayleyEquationCoefficientUnique :
  (c : Nat → CD.RationalComplex) →
  SatisfiesOriginalCayleyEquation c →
  (n : Nat) →
  c n ≡ Formal.cayleyFormalCoefficient n
originalCayleyEquationCoefficientUnique c equation =
  Formal.originalCayleyFormalCoefficientUnique c
    (originalEquationForcesRecurrence c equation)

canonicalCayleyEquation :
  SatisfiesOriginalCayleyEquation Formal.cayleyFormalCoefficient
canonicalCayleyEquation = record
  { coefficientEquation = Formal.cayleyAllDegreeFormalEquation }
