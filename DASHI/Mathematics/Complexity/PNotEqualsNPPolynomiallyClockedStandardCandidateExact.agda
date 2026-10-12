module DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact where

------------------------------------------------------------------------
-- EXPLICIT POLYNOMIAL CLOCK ON THE CONVENTIONAL FINITE STANDARD TM
--
-- This is the ordinary machine-model version of the earlier tape-clock wrapper.
-- The actual execution is the existing StandardExactRun; conversion to the
-- repository ConcreteTapeMachine preserves the same T exactly and pays only
-- static first-match lookup / linear padding overhead in the existing
-- ConcreteTapeStandardClockExact lane.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as StandardCandidate
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.ConcreteTapeStandardClockExact as ClockBridge

natPower : Nat → Nat → Nat
natPower base zero = suc zero
natPower base (suc exponent) = base * natPower base exponent

polynomialStepBudget :
  Nat → Nat → Cook.BooleanFormula → Nat
polynomialStepBudget coefficient degree formula =
  coefficient
  * natPower (suc (Size.formulaNodeCount formula)) degree

record PolynomiallyClockedStandardCandidate
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₂ where
  field
    standard : StandardCandidate.StandardFiniteCandidateCode candidate

    clockCoefficient : Nat
    clockDegree : Nat

    exactStepsPolynomialBound :
      (formula : Cook.BooleanFormula) →
      StandardCandidate.exactSteps standard formula
      ≤ polynomialStepBudget clockCoefficient clockDegree formula

open PolynomiallyClockedStandardCandidate public

------------------------------------------------------------------------
-- Existing standard/concrete clock receipt is automatic for the same program.
------------------------------------------------------------------------

candidateConcreteClockReceipt :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (clocked : PolynomiallyClockedStandardCandidate candidate) →
  ClockBridge.ConcreteStandardClockReceipt
    (StandardCandidate.candidateConcreteMachine (standard clocked))
candidateConcreteClockReceipt clocked =
  ClockBridge.concreteStandardClockReceipt
    (StandardCandidate.candidateConcreteMachine (standard clocked))

------------------------------------------------------------------------
-- FRONTIER
--
-- The standard-machine part of model coverage is now exactly:
--
--   candidate -> finite presented deterministic single-tape program
--             -> genuine finite state/symbol coverage
--             -> formula input encoder
--             -> exact standard execution
--             -> exact final decision bit
--             -> arithmetic polynomial step bound.
--
-- Once such a witness is supplied, the existing exact standard/concrete bridge
-- automatically supplies the concrete Cook--Levin execution semantics.
------------------------------------------------------------------------
