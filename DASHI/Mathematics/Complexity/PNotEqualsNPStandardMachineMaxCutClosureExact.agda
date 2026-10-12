module DASHI.Mathematics.Complexity.PNotEqualsNPStandardMachineMaxCutClosureExact where

------------------------------------------------------------------------
-- CONVENTIONAL STANDARD-TM MAX-CUT -> SAT NOT IN P -> P != NP
--
-- The repository's exact finite standard<->concrete machine equivalence lets
-- us remove the branch-local total ConcreteTape successor from the critical
-- path. The remaining proof obligations are now:
--
--   A. StandardPolynomialCandidateCoverage
--      Every candidate admitted by the selected polynomial cost model has a
--      finite-presented deterministic single-tape realization, exact guarded
--      execution, exact final decision bit, and arithmetic polynomial clock.
--
--   B. FixedProgramCompiler
--      Compile the already-paid abstract finite opposite fixed program into one
--      finite-presented standard TM, with exact terminating semantics when its
--      formula parameter is that same machine's guarded Cook formula.
--
-- B is strictly below an ad-hoc self-quotation axiom: the opposite endpoint law
-- is derived from compiler correctness + the existing `fixedRunExact` theorem.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as StandardCandidate
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedProgramStandardCompilerExact as ProgramCompiler

------------------------------------------------------------------------
-- A: ordinary standard-machine coverage of the selected P predicate.
------------------------------------------------------------------------

record StandardPolynomialCandidateCoverage
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₃ where
  field
    realize :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Clocked.PolynomiallyClockedStandardCandidate candidate

open StandardPolynomialCandidateCoverage public

candidateStandardCode :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  StandardCandidate.StandardFiniteCandidateCode candidate
candidateStandardCode coverage candidate =
  Clocked.standard (realize coverage candidate)

------------------------------------------------------------------------
-- B: compile the already-paid fixed finite program to the standard TM model.
------------------------------------------------------------------------

record FixedProgramCompiler
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) : Set₃ where
  field
    compile :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      ProgramCompiler.FixedProgramStandardCompilation
        (StandardCandidate.standardCandidateToCodeRealization
          (candidateStandardCode coverage candidate))

open FixedProgramCompiler public

------------------------------------------------------------------------
-- A+B -> explicit SAT error for every admitted polynomial candidate.
------------------------------------------------------------------------

standardMaxCutGivesCandidateFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost)
    (compiler : FixedProgramCompiler coverage)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Direct.SATDecisionFailure candidate
standardMaxCutGivesCandidateFailure coverage compiler candidate =
  ProgramCompiler.fixedProgramCompilationGivesDecisionFailure
    (StandardCandidate.standardCandidateToCodeRealization
      (candidateStandardCode coverage candidate))
    (compile compiler candidate)

standardMaxCutGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) →
  FixedProgramCompiler coverage →
  Direct.UniversalPolynomialSATDecisionFailure cost
standardMaxCutGivesUniversalFailure coverage compiler candidate =
  standardMaxCutGivesCandidateFailure coverage compiler candidate

standardMaxCutGivesSATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) →
  FixedProgramCompiler coverage →
  Clay.SATNotInP cost
standardMaxCutGivesSATNotInP coverage compiler =
  Direct.universalDecisionFailureGivesSATNotInP
    (standardMaxCutGivesUniversalFailure coverage compiler)

standardMaxCutGivesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (background : Clay.PNotEqualsNPEstablishedBackground cost)
    (coverage : StandardPolynomialCandidateCoverage cost) →
  FixedProgramCompiler coverage →
  Clay.PNotEqualsNP cost
standardMaxCutGivesPNotEqualsNP background coverage compiler =
  Clay.satNotInPImpliesPNotEqualsNP
    (Clay.satInNP background)
    (standardMaxCutGivesSATNotInP coverage compiler)

------------------------------------------------------------------------
-- EXACT FRONTIER
--
-- Paid below this surface:
--   * finite standard syntax <-> deterministic ConcreteTapeMachine;
--   * exact T-step run transport in both directions;
--   * guarded acceptance iff;
--   * exact clock identity + linear rule-table/padding overhead;
--   * literal candidate static-program code;
--   * Cook--Levin exact-budget iff;
--   * finite partial Kleene/self-specialization machinery;
--   * fixed abstract opposite-program equation;
--   * fixed-program compiler -> opposite endpoint -> SAT failure plumbing.
--
-- Remaining theorem families:
--
--   A. MODEL IDENTIFICATION
--      justify StandardPolynomialCandidateCoverage for the chosen definition
--      of polynomial time. The current abstract PolynomialCostModel cannot do
--      this parametrically because its decider predicate carries no program.
--
--   B. COMPILATION + TERMINATION
--      inhabit FixedProgramCompiler: compile the already-paid finite opposite
--      fixed computation into a finite standard TM and prove its exact finite
--      execution when parameterized by its own guarded Cook formula.
--
-- B includes the resource-closing termination theorem that the ordinary
-- partial recursion theorem intentionally does not provide.
------------------------------------------------------------------------
