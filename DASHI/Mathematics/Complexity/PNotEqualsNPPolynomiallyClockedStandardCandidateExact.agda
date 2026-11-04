module DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact where

------------------------------------------------------------------------
-- EXPLICIT POLYNOMIAL CLOCK ON THE CONVENTIONAL FINITE STANDARD TM
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as StandardCandidate
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as ClockArithmetic
import DASHI.Mathematics.Complexity.ConcreteTapeStandardClockExact as ClockBridge

polynomialStepBudget :
  Nat → Nat → Cook.BooleanFormula → Nat
polynomialStepBudget = ClockArithmetic.formulaPolynomialBudget

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
-- Once this witness is supplied, the existing exact standard/concrete bridge
-- automatically supplies the concrete Cook--Levin execution semantics. Clock
-- arithmetic is shared with the low-universe coded-decider representation.
------------------------------------------------------------------------
