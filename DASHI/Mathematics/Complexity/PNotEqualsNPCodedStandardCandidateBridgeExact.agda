module DASHI.Mathematics.Complexity.PNotEqualsNPCodedStandardCandidateBridgeExact where

------------------------------------------------------------------------
-- SET-LEVEL CODED STANDARD DECIDER -> CLAY-FACING STANDARD CANDIDATE
--
-- This is the representation projection missing from the abstract cost-model
-- lane. Given a literal CodedStandardPolynomialDecider for the SAME extensional
-- decision function carried by a PolynomialSATDeciderCandidate, all higher
-- standard-machine candidate/code/clock receipts are derived directly.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as StandardCandidate
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as CodedDecider
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded

------------------------------------------------------------------------
-- First the exact finite standard candidate implementation.
------------------------------------------------------------------------

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
      CodedDecider.exactSteps witness
  ; StandardCandidate.finish =
      CodedDecider.finish witness
  ; StandardCandidate.execution =
      CodedDecider.execution witness
  ; StandardCandidate.decisionExact =
      CodedDecider.decisionExact witness
  }

------------------------------------------------------------------------
-- Then retain the arithmetic polynomial clock exactly.
------------------------------------------------------------------------

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
      CodedDecider.exactStepsPolynomialBound witness
  }

------------------------------------------------------------------------
-- Candidate-wide coded coverage is exactly sufficient for A.
------------------------------------------------------------------------

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
-- A is no longer a machine-representation theorem. A `Set`-level coded
-- standard-machine witness projects all the way to the exact finite standard
-- candidate and polynomial clock used by the diagonal lane.
--
-- The remaining A-side theorem is cost-model identification/closure:
-- show that the selected `polynomialTimeDecider` predicate supplies this coded
-- witness (ideally by defining the standard model that way) while also paying
-- PolynomialCostModel's map/precomposition/verifier closure fields.
------------------------------------------------------------------------
