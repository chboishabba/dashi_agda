module DASHI.Foundations.BishopMachinOriginalCayleyPhaseCompositionExact where

------------------------------------------------------------------------
-- P1 finite maximum-cut: the TWO independently verified original
-- Machin Gaussian Cayley point-values compose to EXACTLY i.
--
-- C(1/5)^4 conjugate(C(1/239)) = i.
--
-- This pays the full rational *phase composition* at both original
-- Machin inputs on the SAME Q[i] source, not merely two point checks.
-- It does NOT yet identify C(t) with Bishop exp(2i atan_B(t)):
-- the source Bishop analytic same-function bridge is still OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Foundations.BishopMachinOriginalCayleyFormalSeriesExact as Formal
import DASHI.Foundations.BishopMachinOriginalCayleyRationalPointAlgebraExact as Points

twoC : CD.RationalComplex → CD.RationalComplex
twoC z = CD._*c_ z z

fourC : CD.RationalComplex → CD.RationalComplex
fourC z = twoC (twoC z)

originalCayleyMachinGaussianPhase : CD.RationalComplex
originalCayleyMachinGaussianPhase =
  CD._*c_
    (fourC Points.cayleyAtOneFifth)
    (CD.conjugateC Points.cayleyAtOneTwoHundredThirtyNinth)

-- A completely finite exact Q[i] computation: the first source
-- Cayley value advances four double angles, the second retreats
-- one double angle, and the phase is +i.
originalCayleyMachinPhaseIsImaginaryUnit :
  originalCayleyMachinGaussianPhase ≡ Formal.imaginaryUnit
originalCayleyMachinPhaseIsImaginaryUnit =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

originalCayleyMachinPhaseRealIsZero :
  CD.re originalCayleyMachinGaussianPhase
  ≡ CD.re Formal.imaginaryUnit
originalCayleyMachinPhaseRealIsZero =
  cong CD.re originalCayleyMachinPhaseIsImaginaryUnit

originalCayleyMachinPhaseImaginaryIsOne :
  CD.im originalCayleyMachinGaussianPhase
  ≡ CD.im Formal.imaginaryUnit
originalCayleyMachinPhaseImaginaryIsOne =
  cong CD.im originalCayleyMachinPhaseIsImaginaryUnit

-- This is the exact rational normalized phase of the REAL
-- original Machin pair; no numerical rounding, pi axiom,
-- extra branch assertion or unnamed complex carrier is used.

-- Even stronger intermediate: the fourth power of the
-- first EXACT Machin Cayley point is i times the second point.
-- This is the finite algebraic lift of the rational tangent
-- identity, with no analytic branch selection.
originalFourfoldFiveEqualsImaginaryTimes239 :
  fourC Points.cayleyAtOneFifth
  ≡ CD._*c_ Formal.imaginaryUnit
      Points.cayleyAtOneTwoHundredThirtyNinth
originalFourfoldFiveEqualsImaginaryTimes239 =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

