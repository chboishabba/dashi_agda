module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeFixedMaxCutClosureExact where

------------------------------------------------------------------------
-- CONCRETE-TAPE FIXED MAX-CUT -> SAT NOT IN P -> P != NP
--
-- This owner is the current dependency-compressed closure theorem.
--
-- Surviving constructive/model obligations:
--
--   A. candidateTape
--      Every polynomial SAT candidate in the selected cost model is realized
--      by one literal deterministic concrete tape program with an explicit
--      arithmetic polynomial step bound.
--
--   B. fixedOpposite
--      For that exact tape-backed candidate code, construct ONE fixed concrete
--      machine/input/clock whose guarded Cook formula is satisfiable iff the
--      canonical opposite fixed computation returns true.
--
-- Everything after A+B is existing theorem plumbing:
--   fixed concrete semantic quotation -> SATDecisionFailure for each candidate
--   -> universal polynomial SAT failure -> SAT not in P
--   -> with established background for the SAME cost model, P != NP.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDeterministicTapeCodeExact as Tape
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedCandidateTapeExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedConcreteTapeSemanticQuotationExact as FixedConcrete

------------------------------------------------------------------------
-- Exact surviving producer.
------------------------------------------------------------------------

record ConcreteTapeFixedMaxCutProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₃ where
  field
    candidateTape :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Clocked.PolynomiallyClockedCandidateTape candidate

    fixedOpposite :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      FixedConcrete.FixedConcreteOppositeRealization
        (Tape.candidateTapeToCodeRealization
          (Clocked.tape (candidateTape candidate)))

open ConcreteTapeFixedMaxCutProducer public

------------------------------------------------------------------------
-- A+B give an explicit SAT error for every polynomial candidate.
------------------------------------------------------------------------

maxCutProducerGivesCandidateFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (producer : ConcreteTapeFixedMaxCutProducer cost)
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Direct.SATDecisionFailure candidate
maxCutProducerGivesCandidateFailure producer candidate =
  FixedConcrete.fixedConcreteRealizationGivesDecisionFailure
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

------------------------------------------------------------------------
-- Clay-core closure at the selected cost model.
------------------------------------------------------------------------

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
      FixedConcrete.FixedConcreteOppositeRealization
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
-- The previous roadmap items are no longer independent blockers:
-- terminal verification, transition semantics, charged DirectDP plumbing,
-- finite candidate code, deterministic run uniqueness, fixed-width structural
-- quotation, and Cook--Levin iff have all been pushed below this surface.
--
-- The exact remaining theorem families are now:
--
--   MODEL-COVERAGE:
--     ConcreteTapeCandidateCoverage cost
--
--   DIAGONAL-CONSTRUCTOR:
--     FixedOppositeSelfQuotationCompiler coverage
--
-- plus established NP background for the same cost model when promoting the
-- SAT lower bound to the repository's P != NP record.
--
-- No theorem in this owner inhabits either open constructor.
------------------------------------------------------------------------
