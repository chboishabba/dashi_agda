module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeFixedMaxCutClosureExact where

------------------------------------------------------------------------
-- CONCRETE-TAPE FIXED MAX-CUT -> SAT NOT IN P -> P != NP
--
-- Surviving obligations:
--
--   A. MODEL COVERAGE
--      Every polynomial SAT candidate in the selected cost model is realized
--      by one literal deterministic concrete tape program with an explicit
--      arithmetic polynomial step bound.
--
--   B. FIXED OPPOSITE ENDPOINT
--      For that exact tape-backed candidate code, construct ONE fixed concrete
--      machine/input/clock whose deterministic final control bit equals
--
--        not D(its own guarded Cook--Levin formula).
--
-- Everything after A+B is inherited theorem plumbing.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDeterministicTapeCodeExact as Tape
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedCandidateTapeExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedOppositeEndpointDecisionExact as Endpoint

record ConcreteTapeFixedMaxCutProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₃ where
  field
    candidateTape :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Clocked.PolynomiallyClockedCandidateTape candidate

    fixedOpposite :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Endpoint.FixedOppositeEndpointDecisionRealization
        (Tape.candidateTapeToCodeRealization
          (Clocked.tape (candidateTape candidate)))

open ConcreteTapeFixedMaxCutProducer public

maxCutProducerGivesCandidateFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (producer : ConcreteTapeFixedMaxCutProducer cost)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Direct.SATDecisionFailure candidate
maxCutProducerGivesCandidateFailure producer candidate =
  Endpoint.endpointDecisionRealizationGivesDecisionFailure
    (Tape.candidateTapeToCodeRealization
      (Clocked.tape
        (candidateTape producer candidate)))
    (fixedOpposite producer candidate)

maxCutProducerGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  ConcreteTapeFixedMaxCutProducer cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
maxCutProducerGivesUniversalFailure producer candidate =
  maxCutProducerGivesCandidateFailure producer candidate

maxCutProducerGivesSATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  ConcreteTapeFixedMaxCutProducer cost →
  Clay.SATNotInP cost
maxCutProducerGivesSATNotInP producer =
  Direct.universalDecisionFailureGivesSATNotInP
    (maxCutProducerGivesUniversalFailure producer)

maxCutProducerGivesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Clay.PNotEqualsNPEstablishedBackground cost →
  ConcreteTapeFixedMaxCutProducer cost →
  Clay.PNotEqualsNP cost
maxCutProducerGivesPNotEqualsNP background producer =
  Clay.satNotInPImpliesPNotEqualsNP
    (Clay.satInNP background)
    (maxCutProducerGivesSATNotInP producer)

------------------------------------------------------------------------
-- Split form for roadmap/accountability.
------------------------------------------------------------------------

record ConcreteTapeCandidateCoverage
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₃ where
  field
    realize :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Clocked.PolynomiallyClockedCandidateTape candidate

open ConcreteTapeCandidateCoverage public

record FixedOppositeSelfQuotationCompiler
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : ConcreteTapeCandidateCoverage cost) : Set₃ where
  field
    compile :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Endpoint.FixedOppositeEndpointDecisionRealization
        (Tape.candidateTapeToCodeRealization
          (Clocked.tape (realize coverage candidate)))

open FixedOppositeSelfQuotationCompiler public

coverageAndCompilerGiveMaxCut :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (coverage : ConcreteTapeCandidateCoverage cost) →
  FixedOppositeSelfQuotationCompiler coverage →
  ConcreteTapeFixedMaxCutProducer cost
coverageAndCompilerGiveMaxCut coverage compiler = record
  { candidateTape = realize coverage
  ; fixedOpposite = compile compiler
  }

------------------------------------------------------------------------
-- CURRENT FRONTIER
--
-- All downstream semantic directions are derived from one endpoint equation.
-- The exact remaining theorem families are therefore:
--
--   MODEL-COVERAGE:
--     ConcreteTapeCandidateCoverage cost
--
--   FIXED SELF-QUOTATION COMPILER:
--     FixedOppositeSelfQuotationCompiler coverage
--
-- plus established NP background for the same cost model when promoting the
-- SAT lower bound to P != NP.
--
-- No theorem in this owner inhabits either open constructor.
------------------------------------------------------------------------
