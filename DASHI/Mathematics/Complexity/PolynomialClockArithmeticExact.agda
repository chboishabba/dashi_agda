module DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact where

------------------------------------------------------------------------
-- SHARED ARITHMETIC POLYNOMIAL CLOCK
--
-- One owner for the concrete clock shape used by the standard/coded P lane:
--
--   c * (1 + |formula|)^d.
--
-- This is deliberately separate from PolynomialCostModel's abstract predicates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size

natPower : Nat → Nat → Nat
natPower base zero = suc zero
natPower base (suc exponent) = base * natPower base exponent

formulaPolynomialBudget :
  Nat → Nat → Cook.BooleanFormula → Nat
formulaPolynomialBudget coefficient degree formula =
  coefficient
  * natPower (suc (Size.formulaNodeCount formula)) degree
