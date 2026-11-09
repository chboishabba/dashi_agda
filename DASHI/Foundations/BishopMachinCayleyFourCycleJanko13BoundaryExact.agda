{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopMachinCayleyFourCycleJanko13BoundaryExact where

------------------------------------------------------------------------
-- ORIGINAL CAYLEY COEFFICIENT PERIOD FOUR, WITH TYPED JANKO STAGE 13.
--
-- The Cayley formal coefficient stream has special constant c0=1
-- and a four-cycle on positive indices:
--   c1=2i, c2=-2, c3=-2i, c4=2, c5=2i, ...
-- In particular c13=c9=c5=c1.
--
-- Independently the original Janko stage atlas assigns J3 the
-- dual arithmetic addresses 13=10+3=9+4.
--
-- We prove both facts and do NOT equate the coefficient carrier
-- Q[i] with a Janko group, modular level, modular j-function,
-- representation or a Monster graded sector.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; cong; sym)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Foundations.BishopMachinOriginalCayleyFormalSeriesExact as Formal
import DASHI.Foundations.SecondRevolutionJankoTarotExact as Janko
import DASHI.Foundations.BishopMachinCayleyEquationForcesCoefficientsExact as Equation

-- Positive degrees recur by multiplication by the *original*
-- rational Gaussian imaginary unit. The degree-zero exception is
-- never silently folded into the four-cycle.

originalCayleyCoefficientFourPeriod :
  (n : Nat) →
  Formal.cayleyFormalCoefficient
    (suc (suc (suc (suc (suc n)))))
  ≡
  Formal.cayleyFormalCoefficient (suc n)
originalCayleyCoefficientFourPeriod zero =
  CD.complexExt Ring.solve-∀ Ring.solve-∀
originalCayleyCoefficientFourPeriod (suc n) =
  cong
    (CD._*c_ Formal.imaginaryUnit)
    (originalCayleyCoefficientFourPeriod n)

-- Thirteen lies in the same nonconstant coefficient phase as one.
originalCayleyThirteenSameAsOne :
  Formal.cayleyFormalCoefficient 13
  ≡ Formal.cayleyFormalCoefficient 1
originalCayleyThirteenSameAsOne =
  trans
    (originalCayleyCoefficientFourPeriod 8)
    (trans
      (originalCayleyCoefficientFourPeriod 4)
      (originalCayleyCoefficientFourPeriod 0))

originalCayleyThirteenIsTwoImaginaryUnits :
  Formal.cayleyFormalCoefficient 13
  ≡ Formal.twoImaginaryUnits
originalCayleyThirteenIsTwoImaginaryUnits =
  originalCayleyThirteenSameAsOne

-- Reuse the ORIGINAL Janko source's exact ordinal charts.
jankoThirdStageIsTenPlusThree :
  10 + Janko.localOffset Janko.janko3
  ≡ Janko.globalAddress Janko.janko3
jankoThirdStageIsTenPlusThree =
  Janko.globalIsTenPlusLocalOffset Janko.janko3

jankoThirdStageIsNinePlusFour :
  9 + (1 + Janko.localOffset Janko.janko3)
  ≡ Janko.globalAddress Janko.janko3
jankoThirdStageIsNinePlusFour =
  Janko.globalIsNinePlusLocalSuccessor Janko.janko3

jankoThirdGlobalStageIsThirteen :
  Janko.globalAddress Janko.janko3 ≡ 13
jankoThirdGlobalStageIsThirteen = refl

-- This lemma is ONLY a shared Nat-index evaluation, not a
-- cross-carrier representation or modular-function identification.
originalCayleyAtJankoThirdGlobalIndex :
  Formal.cayleyFormalCoefficient
    (Janko.globalAddress Janko.janko3)
  ≡ Formal.cayleyFormalCoefficient 1
originalCayleyAtJankoThirdGlobalIndex =
  originalCayleyThirteenSameAsOne

-- Stronger P1.01 transport: any coefficient family satisfying the
-- original denominator equation inherits the *same* four-period.
-- This uses no separate recurrence or stage-specific oracle.
originalEquationForcesFourPeriod :
  (c : Nat → CD.RationalComplex) →
  Equation.SatisfiesOriginalCayleyEquation c →
  (n : Nat) →
  c (suc (suc (suc (suc (suc n))))) ≡ c (suc n)
originalEquationForcesFourPeriod c equation n =
  trans
    (Equation.originalCayleyEquationCoefficientUnique
      c equation (suc (suc (suc (suc (suc n))))))
    (trans
      (originalCayleyCoefficientFourPeriod n)
      (sym
        (Equation.originalCayleyEquationCoefficientUnique
          c equation (suc n))))

originalEquationForcesStage13Phase :
  (c : Nat → CD.RationalComplex) →
  Equation.SatisfiesOriginalCayleyEquation c →
  c (Janko.globalAddress Janko.janko3) ≡ c 1
originalEquationForcesStage13Phase c equation =
  trans
    (Equation.originalCayleyEquationCoefficientUnique c equation 13)
    (trans
      originalCayleyThirteenSameAsOne
      (sym (Equation.originalCayleyEquationCoefficientUnique
        c equation 1)))
