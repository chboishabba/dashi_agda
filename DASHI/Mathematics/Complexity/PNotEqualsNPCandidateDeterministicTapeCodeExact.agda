module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDeterministicTapeCodeExact where

------------------------------------------------------------------------
-- CANDIDATE CODE AS ONE LITERAL DETERMINISTIC CONCRETE TAPE PROGRAM
--
-- CandidateCodeRealization currently permits an arbitrary code type and an
-- extensional runCandidateCode function.  This owner replaces that loose code
-- witness by one same-object concrete tape program whose output is read from
-- the deterministic final control state.
--
-- The code carrier is the literal fixed-width static-program bit vector of the
-- exact machine.  The proof-heavy decoded program description remains
-- available separately as a receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as ProgramCode
import DASHI.Mathematics.Complexity.PNotEqualsNPDeterministicConcreteTapeExecutionExact as Deterministic

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Locality
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Exact
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Read the result from the actual final control state.
------------------------------------------------------------------------

endpointDecision :
  ∀ {machine : Local.ConcreteTapeMachine}
    {row : Local.TapeRow machine} →
  Locality.InteriorHeadConfiguration machine row →
  Bool
endpointDecision {machine} interior =
  Local.decideEqual
    (Local.finiteState machine)
    (Locality.headState interior)
    (Local.acceptingState machine)

endpointDecisionTrueGivesAccepting :
  ∀ {machine : Local.ConcreteTapeMachine}
    {row : Local.TapeRow machine}
    (interior : Locality.InteriorHeadConfiguration machine row) →
  endpointDecision interior ≡ true →
  Accepting.AcceptingInteriorRow machine row
endpointDecisionTrueGivesAccepting {machine} interior exact = record
  { Accepting.interior = interior
  ; Accepting.headIsAccepting =
      Local.decideEqualSound
        (Local.finiteState machine)
        exact
  }

acceptingGivesEndpointDecisionTrue :
  ∀ {machine : Local.ConcreteTapeMachine}
    {row : Local.TapeRow machine}
    (accepting : Accepting.AcceptingInteriorRow machine row) →
  endpointDecision (Accepting.interior accepting) ≡ true
acceptingGivesEndpointDecisionTrue {machine} accepting
    rewrite Accepting.headIsAccepting accepting =
  Local.decideEqualRefl
    (Local.finiteState machine)
    (Local.acceptingState machine)

------------------------------------------------------------------------
-- Same-object deterministic candidate program.
------------------------------------------------------------------------

record CandidateDeterministicTapeCode
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₂ where
  field
    machine : Local.ConcreteTapeMachine

    stateCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteState machine)

    symbolCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteSymbol machine)

    successor :
      Deterministic.DeterministicTapeSuccessor machine

    successorComplete :
      Deterministic.DeterministicRefinementComplete
        machine
        successor

    encodeFormula :
      Cook.BooleanFormula →
      Input.InputWord machine

    exactSteps :
      Cook.BooleanFormula →
      Nat

    finish :
      Cook.BooleanFormula →
      Local.TapeRow machine

    execution :
      (formula : Cook.BooleanFormula) →
      Deterministic.DeterministicExecution
        successor
        (exactSteps formula)
        (Guard.guardedInitialRow
          (encodeFormula formula)
          (exactSteps formula))
        (finish formula)

    initialEndpoint :
      (formula : Cook.BooleanFormula) →
      Accepting.InitialInteriorRow
        machine
        (Guard.guardedInitialRow
          (encodeFormula formula)
          (exactSteps formula))

    finalInterior :
      (formula : Cook.BooleanFormula) →
      Locality.InteriorHeadConfiguration
        machine
        (finish formula)

    decisionExact :
      (formula : Cook.BooleanFormula) →
      endpointDecision (finalInterior formula)
      ≡
      Direct.decide candidate formula

open CandidateDeterministicTapeCode public

------------------------------------------------------------------------
-- Literal static machine code and exact code size.
------------------------------------------------------------------------

candidateProgramBits :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : CandidateDeterministicTapeCode candidate) →
  CNF.Bits (ProgramCode.StaticProgramBitsWidth (machine tape))
candidateProgramBits tape =
  ProgramCode.encodeStaticProgram
    (machine tape)
    (stateCoverage tape)
    (symbolCoverage tape)

candidateProgramDescription :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : CandidateDeterministicTapeCode candidate) →
  ProgramCode.ConcreteTapeProgramDescription
    (machine tape)
candidateProgramDescription tape =
  ProgramCode.canonicalConcreteTapeProgramDescription
    (machine tape)
    (stateCoverage tape)
    (symbolCoverage tape)

candidateProgramBitSize :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  CandidateDeterministicTapeCode candidate →
  Nat
candidateProgramBitSize tape =
  ProgramCode.StaticProgramBitsWidth (machine tape)

------------------------------------------------------------------------
-- Tighten CandidateCodeRealization to the literal bit-vector code.
------------------------------------------------------------------------

candidateTapeToCodeRealization :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  CandidateDeterministicTapeCode candidate →
  Actual.CandidateCodeRealization candidate
candidateTapeToCodeRealization tape = record
  { Actual.CandidateCode =
      CNF.Bits
        (ProgramCode.StaticProgramBitsWidth
          (machine tape))
  ; Actual.candidateCode =
      candidateProgramBits tape
  ; Actual.runCandidateCode =
      λ codeBits formula →
        endpointDecision (finalInterior tape formula)
  ; Actual.codeDecisionExact =
      decisionExact tape
  ; Actual.codeSize =
      λ codeBits → candidateProgramBitSize tape
  }

------------------------------------------------------------------------
-- Candidate=true gives the actual deterministic accepting run.
------------------------------------------------------------------------

candidateTrueGivesExactBudgetRun :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : CandidateDeterministicTapeCode candidate)
    (formula : Cook.BooleanFormula) →
  Direct.decide candidate formula ≡ true →
  Exact.ExactBudgetAcceptingRun
    (encodeFormula tape formula)
    (exactSteps tape formula)
candidateTrueGivesExactBudgetRun tape formula candidateTrue =
  Deterministic.deterministicExecutionToExactBudgetAcceptingRun
    (encodeFormula tape formula)
    (exactSteps tape formula)
    (execution tape formula)
    (initialEndpoint tape formula)
    (endpointDecisionTrueGivesAccepting
      (finalInterior tape formula)
      endpointTrue)
  where
    endpointTrue :
      endpointDecision (finalInterior tape formula) ≡ true
    endpointTrue =
      trans
        (decisionExact tape formula)
        candidateTrue

------------------------------------------------------------------------
-- Conversely, any relational exact-budget accepting run must coincide with
-- the deterministic endpoint, hence the candidate bit is true.
------------------------------------------------------------------------

exactBudgetRunGivesCandidateTrue :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : CandidateDeterministicTapeCode candidate)
    (formula : Cook.BooleanFormula) →
  Exact.ExactBudgetAcceptingRun
    (encodeFormula tape formula)
    (exactSteps tape formula) →
  Direct.decide candidate formula ≡ true
exactBudgetRunGivesCandidateTrue tape formula exact =
  trans
    (sym (decisionExact tape formula))
    (acceptingGivesEndpointDecisionTrue deterministicAccepting)
  where
    deterministicAccepting :
      Accepting.AcceptingInteriorRow
        (machine tape)
        (finish tape formula)
    deterministicAccepting =
      Deterministic.exactBudgetRunForcesDeterministicAccepting
        (successorComplete tape)
        (encodeFormula tape formula)
        (exactSteps tape formula)
        (execution tape formula)
        exact

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- CandidateCodeRealization is now literally fixed-width machine bits; its size
-- is the static-program bit width and its decision bit is read from the exact
-- deterministic final control state.
--
-- Remaining universal debt:
--   every executable SAT candidate must be lowered to such a deterministic
--   tape program, and the opposite interpreter must combine program quotation,
--   candidate execution and Boolean negation in one concrete machine.
------------------------------------------------------------------------
