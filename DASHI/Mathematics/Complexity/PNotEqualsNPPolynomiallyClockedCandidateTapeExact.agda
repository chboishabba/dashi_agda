module DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedCandidateTapeExact where

------------------------------------------------------------------------
-- EXPLICIT ARITHMETIC POLYNOMIAL CLOCK FOR CONCRETE TAPE CANDIDATES
--
-- PolynomialCostModel deliberately leaves "polynomial" abstract.  For the
-- literal concrete-tape realization we also retain an ordinary arithmetic
-- step bound:
--
--   exactSteps(phi) <= c * (1 + |phi|)^d.
--
-- This does not replace the selected PolynomialCostModel certificate; it is an
-- additional same-machine quantitative receipt connecting the actual tape
-- execution to a standard polynomial clock shape.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDeterministicTapeCodeExact as Tape
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size

natPower : Nat → Nat → Nat
natPower base zero =
  suc zero
natPower base (suc exponent) =
  base * natPower base exponent

polynomialStepBudget :
  Nat → Nat → Cook.BooleanFormula → Nat
polynomialStepBudget coefficient degree formula =
  coefficient
  *
  natPower
    (suc (Size.formulaNodeCount formula))
    degree

record PolynomiallyClockedCandidateTape
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₂ where
  field
    tape :
      Tape.CandidateDeterministicTapeCode candidate

    clockCoefficient : Nat
    clockDegree : Nat

    exactStepsPolynomialBound :
      (formula : Cook.BooleanFormula) →
      Tape.exactSteps tape formula
      ≤
      polynomialStepBudget
        clockCoefficient
        clockDegree
        formula

open PolynomiallyClockedCandidateTape public

------------------------------------------------------------------------
-- Boundary: extensional polynomial evidence and concrete arithmetic clock are
-- distinct receipts and neither is silently manufactured from the other.
------------------------------------------------------------------------

record PolynomialClockBoundary : Set where
  constructor polynomial-clock-boundary
  field
    extensionalPolynomialCertificateRetained : Agda.Builtin.Bool.Bool
    actualTapeExecutionBounded : Agda.Builtin.Bool.Bool
    abstractCostPredicateDefinesArithmeticClock : Agda.Builtin.Bool.Bool

open import Agda.Builtin.Bool using (false; true)

canonicalPolynomialClockBoundary : PolynomialClockBoundary
canonicalPolynomialClockBoundary =
  polynomial-clock-boundary
    true true false
