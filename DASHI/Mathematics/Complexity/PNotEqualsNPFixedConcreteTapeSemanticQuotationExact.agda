module DASHI.Mathematics.Complexity.PNotEqualsNPFixedConcreteTapeSemanticQuotationExact where

------------------------------------------------------------------------
-- ONE FIXED CONCRETE TAPE EXECUTION -> OPPOSITE SEMANTIC QUOTATION
--
-- FixedOppositeSemanticQuotationExact shows that the diagonal theorem needs
-- semantic correctness only for the canonical opposite fixed program.
-- Therefore the concrete realization can also be specialized to ONE literal
-- machine/input/clock tuple.
--
-- The quoted Cook formula is definitionally the existing guarded Cook--Levin
-- formula for that exact tuple.  Deterministic execution and endpoint
-- correctness derive SAT iff fixed abstract run returns true.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Unit using (tt)
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedOppositeSemanticQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPDeterministicConcreteTapeExecutionExact as Deterministic

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Exact
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin

------------------------------------------------------------------------
-- Finite concrete machine/input/clock data.
------------------------------------------------------------------------

record FixedConcreteOppositeMachine
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    machine : Local.ConcreteTapeMachine

    stateCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteState machine)

    symbolCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteSymbol machine)

    nonemptyRules :
      Selector.NonemptyRuleTable machine

    input :
      Input.InputWord machine

    steps :
      Agda.Builtin.Nat.Nat

open FixedConcreteOppositeMachine public

fixedCookFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  FixedConcreteOppositeMachine code →
  Cook.BooleanFormula
fixedCookFormula concrete =
  CookLevin.guardedCookFormula
    (stateCoverage concrete)
    (symbolCoverage concrete)
    (nonemptyRules concrete)
    (input concrete)
    (steps concrete)

------------------------------------------------------------------------
-- Deterministic same-object execution and endpoint semantics.
------------------------------------------------------------------------

record FixedConcreteOppositeRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    concrete :
      FixedConcreteOppositeMachine code

    successor :
      Deterministic.DeterministicTapeSuccessor
        (machine concrete)

    successorComplete :
      Deterministic.DeterministicRefinementComplete
        (machine concrete)
        successor

    finish :
      Local.TapeRow (machine concrete)

    execution :
      Deterministic.DeterministicExecution
        successor
        (steps concrete)
        (Guard.guardedInitialRow
          (input concrete)
          (steps concrete))
        finish

    initialEndpoint :
      Accepting.InitialInteriorRow
        (machine concrete)
        (Guard.guardedInitialRow
          (input concrete)
          (steps concrete))

    fixedRunTrueGivesAcceptingEndpoint :
      Fixed.fixedRun code (fixedCookFormula concrete)
      ≡ just true →
      Accepting.AcceptingInteriorRow
        (machine concrete)
        finish

    acceptingEndpointGivesFixedRunTrue :
      Accepting.AcceptingInteriorRow
        (machine concrete)
        finish →
      Fixed.fixedRun code (fixedCookFormula concrete)
      ≡ just true

open FixedConcreteOppositeRealization public

------------------------------------------------------------------------
-- Compile to the fixed semantic quotation.
------------------------------------------------------------------------

fixedConcreteToSemanticQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  FixedConcreteOppositeRealization code →
  Fixed.FixedSemanticQuotation code
fixedConcreteToSemanticQuotation realization = record
  { Fixed.formula =
      fixedCookFormula (concrete realization)

  ; Fixed.trueRunGivesSAT =
      λ returnedTrue →
        CookLevin.exactBudgetRunToCookSatisfiable
          (stateCoverage (concrete realization))
          (symbolCoverage (concrete realization))
          (nonemptyRules (concrete realization))
          (input (concrete realization))
          (steps (concrete realization))
          (Deterministic.deterministicExecutionToExactBudgetAcceptingRun
            (input (concrete realization))
            (steps (concrete realization))
            (execution realization)
            (initialEndpoint realization)
            (fixedRunTrueGivesAcceptingEndpoint
              realization
              returnedTrue))

  ; Fixed.satGivesTrueRun =
      λ satisfiable →
        acceptingEndpointGivesFixedRunTrue
          realization
          (Deterministic.exactBudgetRunForcesDeterministicAccepting
            (successorComplete realization)
            (input (concrete realization))
            (steps (concrete realization))
            (execution realization)
            (CookLevin.cookSatisfiableToExactBudgetRun
              (stateCoverage (concrete realization))
              (symbolCoverage (concrete realization))
              (nonemptyRules (concrete realization))
              (input (concrete realization))
              (steps (concrete realization))
              satisfiable))
  }

fixedConcreteRealizationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  FixedConcreteOppositeRealization code →
  Direct.SATDecisionFailure candidate
fixedConcreteRealizationGivesDecisionFailure code realization =
  Fixed.fixedSemanticQuotationGivesDecisionFailure
    code
    (fixedConcreteToSemanticQuotation realization)

record FixedConcreteOppositeProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₃ where
  field
    candidateCode :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Actual.CandidateCodeRealization candidate

    realization :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      FixedConcreteOppositeRealization
        (candidateCode candidate)

open FixedConcreteOppositeProducer public

fixedConcreteProducerGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  FixedConcreteOppositeProducer cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
fixedConcreteProducerGivesUniversalFailure producer candidate =
  fixedConcreteRealizationGivesDecisionFailure
    (candidateCode producer candidate)
    (realization producer candidate)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Removed from the concrete wall:
--   * arbitrary program inputs;
--   * a universal finite-program interpreter;
--   * semantic correctness for all programs.
--
-- The surviving constructor is one fixed same-object machine tuple whose
-- behavior is:
--
--   accept  iff  not D(its own guarded Cook--Levin formula).
--
-- Constructing that finite machine/self-quotation with honest static size and
-- exact clock is now the singular execution frontier.
------------------------------------------------------------------------
