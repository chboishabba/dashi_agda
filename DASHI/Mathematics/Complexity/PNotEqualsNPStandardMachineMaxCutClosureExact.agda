module DASHI.Mathematics.Complexity.PNotEqualsNPStandardMachineMaxCutClosureExact where

------------------------------------------------------------------------
-- CONVENTIONAL STANDARD-TM MAX-CUT -> SAT NOT IN P -> P != NP
--
-- The repository's exact finite standard<->concrete machine equivalence lets
-- us remove branch-local concrete execution artifacts from the critical path.
-- The remaining proof obligations are now:
--
--   A. StandardPolynomialCandidateCoverage
--      Every candidate admitted by the selected polynomial cost model has a
--      finite-presented deterministic single-tape realization, exact guarded
--      execution, exact final decision bit, and arithmetic polynomial clock.
--
--   B. ResourceClosingCompiler
--      Construct one fixed finite standard machine exposing, rather than hiding,
--      the three phases:
--
--        prefix/self-quotation setup
--          ; edge-for-edge simulation of D on its own Cook formula
--          ; finite Boolean-negation suffix,
--
--      with exact additive closure to the Cook budget T.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as StandardCandidate
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as ResourceCompiler
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
-- B: resource-closing compiler with the candidate subrun made explicit.
------------------------------------------------------------------------

record ResourceClosingCompiler
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) : Set₃ where
  field
    compile :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      ResourceCompiler.ResourceClosingFixedProgramCompilation
        (realize coverage candidate)

open ResourceClosingCompiler public

resourceClosingCompilerToFixedProgramCompiler :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {coverage : StandardPolynomialCandidateCoverage cost} →
  ResourceClosingCompiler coverage →
  (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  ProgramCompiler.FixedProgramStandardCompilation
    (StandardCandidate.standardCandidateToCodeRealization
      (candidateStandardCode coverage candidate))
resourceClosingCompilerToFixedProgramCompiler
    {coverage = coverage}
    compiler candidate =
  ResourceCompiler.resourceClosingToFixedProgramCompilation
    (compile compiler candidate)

------------------------------------------------------------------------
-- A+B -> explicit SAT error for every admitted polynomial candidate.
------------------------------------------------------------------------

standardMaxCutGivesCandidateFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost)
    (compiler : ResourceClosingCompiler coverage)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Direct.SATDecisionFailure candidate
standardMaxCutGivesCandidateFailure coverage compiler candidate =
  ProgramCompiler.fixedProgramCompilationGivesDecisionFailure
    (StandardCandidate.standardCandidateToCodeRealization
      (candidateStandardCode coverage candidate))
    (resourceClosingCompilerToFixedProgramCompiler compiler candidate)

standardMaxCutGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) →
  ResourceClosingCompiler coverage →
  Direct.UniversalPolynomialSATDecisionFailure cost
standardMaxCutGivesUniversalFailure coverage compiler candidate =
  standardMaxCutGivesCandidateFailure coverage compiler candidate

standardMaxCutGivesSATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) →
  ResourceClosingCompiler coverage →
  Clay.SATNotInP cost
standardMaxCutGivesSATNotInP coverage compiler =
  Direct.universalDecisionFailureGivesSATNotInP
    (standardMaxCutGivesUniversalFailure coverage compiler)

standardMaxCutGivesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (background : Clay.PNotEqualsNPEstablishedBackground cost)
    (coverage : StandardPolynomialCandidateCoverage cost) →
  ResourceClosingCompiler coverage →
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
--   * step-preserving standard-machine simulation;
--   * explicit candidate-own-formula middle run and inherited polynomial bound;
--   * phase concatenation / exact total-time transport;
--   * resource-closing compiler -> opposite endpoint -> SAT failure plumbing.
--
-- Remaining theorem families:
--
--   A. MODEL IDENTIFICATION / CODING
--      justify StandardPolynomialCandidateCoverage for the selected definition
--      of polynomial time. The current abstract PolynomialCostModel cannot do
--      this parametrically because its decider predicate carries no finite
--      program. A fixed low-universe coded standard-machine/interpreter model
--      would make this identification canonical.
--
--   B. SELF-QUOTATION PREFIX / RESOURCE CLOSURE
--      inhabit ResourceClosingCompiler. The candidate run itself is no longer
--      hidden: the residual is to construct the fixed finite target program and
--      its prefix so that the target's OWN guarded Cook formula is presented as
--      the literal candidate input, while prefix + candidate + suffix closes to
--      the same exact T used in that Cook formula.
--
-- Ordinary partial recursion/self-specialization does not pay B because it does
-- not prove this terminating finite-resource closure.
------------------------------------------------------------------------
