module DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact where

------------------------------------------------------------------------
-- SHARED ARITHMETIC POLYNOMIAL CLOCK
--
-- The size variable is the length of the repository's actual canonical binary
-- formula serialization, not merely AST node count.  In particular variable
-- indices are serialized through Nat prefix tokens, so their representation
-- length is charged honestly.
--
--   T(phi) = c * (1 + bitCodeLength(phi))^d.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

natPower : Nat → Nat → Nat
natPower base zero = suc zero
natPower base (suc exponent) = base * natPower base exponent

formulaPolynomialBudget :
  Nat → Nat → Cook.BooleanFormula → Nat
formulaPolynomialBudget coefficient degree formula =
  coefficient
  * natPower (suc (Binary.formulaBitCodeLength formula)) degree
