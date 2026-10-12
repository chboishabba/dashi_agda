module DASHI.Mathematics.Complexity.PNotEqualsNPCodedStandardCandidateBridgeExact where

------------------------------------------------------------------------
-- SET-LEVEL CODED STANDARD DECIDER -> CLAY-FACING STANDARD CANDIDATE
------------------------------------------------------------------------

import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as StandardCandidate
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as CodedDecider
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded

codedWitnessToStandardCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  CodedDecider.CodedStandardPolynomialDecider
    (Direct.decide candidate) →
  StandardCandidate.StandardFiniteCandidateCode candidate
codedWitnessToStandardCandidate witness = record
  { StandardCandidate.presentation =
      Coded.decodeCodedStandardTM
        (CodedDecider.code witness)
  ; StandardCandidate.stateCoverage =
      Coded.codedStateCoverage
        (CodedDecider.code witness)
  ; StandardCandidate.symbolCoverage =
      Coded.codedSymbolCoverage
        (CodedDecider.code witness)
  ; StandardCandidate.encodeFormula =
      CodedDecider.formulaInput
        (CodedDecider.code witness)
        (CodedDecider.zeroSymbol witness)
        (CodedDecider.oneSymbol witness)
  ; StandardCandidate.exactSteps =
      CodedDecider.polynomialStepBudget
        (CodedDecider.clockCoefficient witness)
        (CodedDecider.clockDegree witness)
  ; StandardCandidate.finish =
      CodedDecider.finish witness
  ; StandardCandidate.execution =
      CodedDecider.execution witness
  ; StandardCandidate.decisionExact =
      CodedDecider.decisionExact witness
  }

codedWitnessToPolynomiallyClockedCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  CodedDecider.CodedStandardPolynomialDecider
    (Direct.decide candidate) →
  Clocked.PolynomiallyClockedStandardCandidate candidate
codedWitnessToPolynomiallyClockedCandidate witness = record
  { Clocked.standard =
      codedWitnessToStandardCandidate witness
  ; Clocked.clockCoefficient =
      CodedDecider.clockCoefficient witness
  ; Clocked.clockDegree =
      CodedDecider.clockDegree witness
  ; Clocked.exactStepsPolynomialBound =
      λ formula → NatP.≤-refl
  }

record CodedStandardCandidateCoverage
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₂ where
  field
    realize :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      CodedDecider.CodedStandardPolynomialDecider
        (Direct.decide candidate)

open CodedStandardCandidateCoverage public

codedCoverageGivesClockedCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : CodedStandardCandidateCoverage cost)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Clocked.PolynomiallyClockedStandardCandidate candidate
codedCoverageGivesClockedCandidate coverage candidate =
  codedWitnessToPolynomiallyClockedCandidate
    (realize coverage candidate)

------------------------------------------------------------------------
-- FRONTIER
--
-- The coded witness projects all the way to the exact finite standard candidate
-- and its clock.  In the coded model the clock bound is reflexive because the
-- exact run length IS the canonical size-only polynomial budget.
------------------------------------------------------------------------
