module DASHI.Mathematics.Complexity.PNotEqualsNPDeterministicOppositeTapeRealizationExact where

------------------------------------------------------------------------
-- DETERMINISTIC OPPOSITE-INTERPRETER REALIZATION
--
-- ConcreteTapeSemanticQuotationBridgeExact currently asks clients to prove two
-- existential run statements directly:
--
--   abstract true -> ExactBudgetAcceptingRun
--   ExactBudgetAcceptingRun -> abstract true.
--
-- The deterministic tape refinement lets us replace those by a stronger and
-- more executable object:
--
--   * one deterministic successor for the exact concrete machine;
--   * one exact deterministic trace for every quoted program;
--   * completeness of that successor against the underlying relational tape
--     semantics;
--   * endpoint correctness: the deterministic final row is accepting iff the
--     abstract opposite interpreter returns true.
--
-- Cook--Levin run existence is then derived, not supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (tt)
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeSemanticQuotationBridgeExact as Concrete
import DASHI.Mathematics.Complexity.PNotEqualsNPDeterministicConcreteTapeExecutionExact as Deterministic

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard

------------------------------------------------------------------------
-- Same-machine deterministic realization.
------------------------------------------------------------------------

record DeterministicOppositeTapeRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    concrete :
      Concrete.ConcreteOppositeInterpreterMachine code

    successor :
      Deterministic.DeterministicTapeSuccessor
        (Concrete.machine concrete)

    successorComplete :
      Deterministic.DeterministicRefinementComplete
        (Concrete.machine concrete)
        successor

    finish :
      Code.Program (Opposite.OppositeQuotedPrimitive code) →
      Local.TapeRow (Concrete.machine concrete)

    execution :
      (program : Code.Program (Opposite.OppositeQuotedPrimitive code)) →
      Deterministic.DeterministicExecution
        successor
        (Concrete.exactSteps concrete program)
        (Guard.guardedInitialRow
          (Concrete.encodeProgram concrete program)
          (Concrete.exactSteps concrete program))
        (finish program)

    initialEndpoint :
      (program : Code.Program (Opposite.OppositeQuotedPrimitive code)) →
      Accepting.InitialInteriorRow
        (Concrete.machine concrete)
        (Guard.guardedInitialRow
          (Concrete.encodeProgram concrete program)
          (Concrete.exactSteps concrete program))

    abstractTrueGivesAcceptingEndpoint :
      (program : Code.Program (Opposite.OppositeQuotedPrimitive code)) →
      Code.run1
        (Opposite.oppositePrimitiveSemantics
          code
          (Concrete.concreteQuotationSurface concrete))
        program
        tt
      ≡ just true →
      Accepting.AcceptingInteriorRow
        (Concrete.machine concrete)
        (finish program)

    acceptingEndpointGivesAbstractTrue :
      (program : Code.Program (Opposite.OppositeQuotedPrimitive code)) →
      Accepting.AcceptingInteriorRow
        (Concrete.machine concrete)
        (finish program) →
      Code.run1
        (Opposite.oppositePrimitiveSemantics
          code
          (Concrete.concreteQuotationSurface concrete))
        program
        tt
      ≡ just true

open DeterministicOppositeTapeRealization public

------------------------------------------------------------------------
-- Compile deterministic execution to the existing semantic-quotation bridge.
------------------------------------------------------------------------

deterministicToConcreteRealization :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  DeterministicOppositeTapeRealization code →
  Concrete.ConcreteOppositeInterpreterRealization code
deterministicToConcreteRealization realization = record
  { Concrete.concrete = concrete realization
  ; Concrete.trueRunToExactBudget =
      λ program returnedTrue →
        Deterministic.deterministicExecutionToExactBudgetAcceptingRun
          (Concrete.encodeProgram (concrete realization) program)
          (Concrete.exactSteps (concrete realization) program)
          (execution realization program)
          (initialEndpoint realization program)
          (abstractTrueGivesAcceptingEndpoint
            realization
            program
            returnedTrue)
  ; Concrete.exactBudgetToTrueRun =
      λ program exactRun →
        acceptingEndpointGivesAbstractTrue
          realization
          program
          (Deterministic.exactBudgetRunForcesDeterministicAccepting
            (successorComplete realization)
            (Concrete.encodeProgram (concrete realization) program)
            (Concrete.exactSteps (concrete realization) program)
            (execution realization program)
            exactRun)
  }

------------------------------------------------------------------------
-- Existing diagonal theorem now consumes the deterministic realization.
------------------------------------------------------------------------

deterministicRealizationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  DeterministicOppositeTapeRealization code →
  Direct.SATDecisionFailure candidate
deterministicRealizationGivesDecisionFailure code realization =
  Concrete.concreteRealizationGivesDecisionFailure
    code
    (deterministicToConcreteRealization realization)

record DeterministicOppositeTapeProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₃ where
  field
    candidateCode :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Actual.CandidateCodeRealization candidate

    realization :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      DeterministicOppositeTapeRealization
        (candidateCode candidate)

open DeterministicOppositeTapeProducer public

deterministicProducerGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  DeterministicOppositeTapeProducer cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
deterministicProducerGivesUniversalFailure producer candidate =
  deterministicRealizationGivesDecisionFailure
    (candidateCode producer candidate)
    (realization producer candidate)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Existential accepting-run semantics have been removed from the primitive
-- realization target. The remaining constructive object is now explicitly:
--
--   candidate code
--     -> SAME concrete deterministic tape machine
--     -> exact program input encoding + exact step count
--     -> exact deterministic execution
--     -> accepting endpoint iff abstract opposite interpreter returns true.
--
-- The next max-cut is therefore the candidate/interpreter compiler and its
-- honest code-size/runtime closure, not another Cook--Levin theorem.
------------------------------------------------------------------------
