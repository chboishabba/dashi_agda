module DASHI.Mathematics.Complexity.PNotEqualsNPFixedConcreteTapeSemanticQuotationExact where

------------------------------------------------------------------------
-- ONE FIXED CONCRETE TAPE EXECUTION -> OPPOSITE SEMANTIC QUOTATION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Nat using (Nat)
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
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin

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

    input : Input.InputWord machine
    steps : Nat

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

record FixedConcreteOppositeRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    concrete : FixedConcreteOppositeMachine code

    successor :
      Deterministic.DeterministicTapeSuccessor
        (machine concrete)

    successorComplete :
      Deterministic.DeterministicRefinementComplete
        (machine concrete)
        successor

    finish : Local.TapeRow (machine concrete)

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
