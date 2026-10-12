module DASHI.Mathematics.Complexity.PNotEqualsNPStandardMachineMaxCutClosureExact where

------------------------------------------------------------------------
-- CONVENTIONAL STANDARD-TM MAX-CUT -> SAT NOT IN P -> P != NP
--
-- The repository's exact finite standard<->concrete machine equivalence lets
-- us remove the branch-local total ConcreteTape successor from the critical
-- path.  The remaining proof obligations can now be stated entirely on the
-- conventional finite-presented deterministic single-tape model.
--
--   A. StandardPolynomialCandidateCoverage
--      Every candidate admitted by the selected polynomial cost model has a
--      finite-presented deterministic single-tape realization, exact guarded
--      execution, exact final decision bit, and arithmetic polynomial clock.
--
--   B. StandardFixedOppositeCompiler
--      For the literal finite code of that candidate, construct ONE finite-
--      presented standard program whose final accepting bit is
--
--        not D(CL(M,x,T))
--
--      for its own exact guarded Cook--Levin formula.
--
-- Existing standard/concrete equivalence + Cook--Levin + the fixed diagonal
-- then derive SATDecisionFailure for every candidate automatically.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as StandardCandidate
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite

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
-- B: one fixed standard-machine behavioral self-quotation per candidate.
------------------------------------------------------------------------

record StandardFixedOppositeCompiler
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) : Set₃ where
  field
    compile :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Opposite.FixedStandardOppositeEndpointRealization
        (StandardCandidate.standardCandidateToCodeRealization
          (candidateStandardCode coverage candidate))

open StandardFixedOppositeCompiler public

------------------------------------------------------------------------
-- A+B -> explicit SAT error for every admitted polynomial candidate.
------------------------------------------------------------------------

standardMaxCutGivesCandidateFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost)
    (compiler : StandardFixedOppositeCompiler coverage)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Direct.SATDecisionFailure candidate
standardMaxCutGivesCandidateFailure coverage compiler candidate =
  Opposite.standardEndpointRealizationGivesDecisionFailure
    (StandardCandidate.standardCandidateToCodeRealization
      (candidateStandardCode coverage candidate))
    (compile compiler candidate)

standardMaxCutGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) →
  StandardFixedOppositeCompiler coverage →
  Direct.UniversalPolynomialSATDecisionFailure cost
standardMaxCutGivesUniversalFailure coverage compiler candidate =
  standardMaxCutGivesCandidateFailure coverage compiler candidate

standardMaxCutGivesSATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : StandardPolynomialCandidateCoverage cost) →
  StandardFixedOppositeCompiler coverage →
  Clay.SATNotInP cost
standardMaxCutGivesSATNotInP coverage compiler =
  Direct.universalDecisionFailureGivesSATNotInP
    (standardMaxCutGivesUniversalFailure coverage compiler)

standardMaxCutGivesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (background : Clay.PNotEqualsNPEstablishedBackground cost)
    (coverage : StandardPolynomialCandidateCoverage cost) →
  StandardFixedOppositeCompiler coverage →
  Clay.PNotEqualsNP cost
standardMaxCutGivesPNotEqualsNP background coverage compiler =
  Clay.satNotInPImpliesPNotEqualsNP
    (Clay.satInNP background)
    (standardMaxCutGivesSATNotInP coverage compiler)

------------------------------------------------------------------------
-- EXACT FRONTIER
--
-- Machine-representation plumbing below A/B is now paid by existing owners:
--
--   finite standard syntax <-> deterministic ConcreteTapeMachine
--   exact T-step run transport in both directions
--   guarded acceptance iff
--   exact clock identity + linear rule-table/padding overhead
--   literal static-program quotation
--   Cook--Levin exact-budget iff
--   fixed-program diagonal contradiction.
--
-- The two remaining theorem families are therefore genuinely higher level:
--
--   MODEL IDENTIFICATION:
--     justify StandardPolynomialCandidateCoverage for the chosen definition of P;
--
--   RECURSION / SELF-QUOTATION:
--     construct StandardFixedOppositeCompiler, i.e. a finite standard machine
--     satisfying finalBit = not D(CL(its own program/input/clock)).
--
-- Neither constructor is inhabited here.
------------------------------------------------------------------------
