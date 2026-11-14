module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeSemanticQuotationBridgeExact where

------------------------------------------------------------------------
-- CONCRETE TAPE REALIZATION -> SEMANTICS-BEARING PROGRAM QUOTATION
--
-- OppositeSemanticProgramQuotationExact reduced the diagonal theorem to one
-- missing object:
--
--   SAT(quoteProgram p)  iff  finite opposite interpreter p returns true.
--
-- The repository's concrete Cook--Levin theorem already supplies exactly the
-- SAT <-> accepting-run half. Therefore all that remains is to realize the
-- finite opposite interpreter by one concrete tape machine with a literal input
-- encoder and exact time budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (tt)
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Exact
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin

------------------------------------------------------------------------
-- First: finite concrete-machine DATA only.
------------------------------------------------------------------------

record ConcreteOppositeInterpreterMachine
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

    encodeProgram :
      Code.Program (Opposite.OppositeQuotedPrimitive code) →
      Input.InputWord machine

    exactSteps :
      Code.Program (Opposite.OppositeQuotedPrimitive code) →
      Nat

open ConcreteOppositeInterpreterMachine public

------------------------------------------------------------------------
-- Quotation is DEFINED from the machine data, never supplied as authority.
------------------------------------------------------------------------

concreteQuotationSurface :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  ConcreteOppositeInterpreterMachine code →
  Opposite.OppositeProgramQuotation code
concreteQuotationSurface concrete = record
  { Opposite.quoteProgram =
      λ program →
        CookLevin.guardedCookFormula
          (stateCoverage concrete)
          (symbolCoverage concrete)
          (nonemptyRules concrete)
          (encodeProgram concrete program)
          (exactSteps concrete program)
  }

------------------------------------------------------------------------
-- Second: prove the abstract finite interpreter and concrete accepting-run
-- semantics coincide. No SAT formula/satisfiability field is present here.
------------------------------------------------------------------------

record ConcreteOppositeInterpreterRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    concrete : ConcreteOppositeInterpreterMachine code

    trueRunToExactBudget :
      (program : Code.Program (Opposite.OppositeQuotedPrimitive code)) →
      Code.run1
        (Opposite.oppositePrimitiveSemantics
          code
          (concreteQuotationSurface concrete))
        program
        tt
      ≡ just true →
      Exact.ExactBudgetAcceptingRun
        (encodeProgram concrete program)
        (exactSteps concrete program)

    exactBudgetToTrueRun :
      (program : Code.Program (Opposite.OppositeQuotedPrimitive code)) →
      Exact.ExactBudgetAcceptingRun
        (encodeProgram concrete program)
        (exactSteps concrete program) →
      Code.run1
        (Opposite.oppositePrimitiveSemantics
          code
          (concreteQuotationSurface concrete))
        program
        tt
      ≡ just true

open ConcreteOppositeInterpreterRealization public

------------------------------------------------------------------------
-- Concrete Cook--Levin gives SemanticProgramQuotation automatically.
------------------------------------------------------------------------

concreteRealizationToSemanticQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  ConcreteOppositeInterpreterRealization code →
  Opposite.SemanticProgramQuotation code
concreteRealizationToSemanticQuotation realization = record
  { Opposite.quotation =
      concreteQuotationSurface
        (concrete realization)

  ; Opposite.trueRunGivesSAT =
      λ program returnedTrue →
        CookLevin.exactBudgetRunToCookSatisfiable
          (stateCoverage (concrete realization))
          (symbolCoverage (concrete realization))
          (nonemptyRules (concrete realization))
          (encodeProgram (concrete realization) program)
          (exactSteps (concrete realization) program)
          (trueRunToExactBudget
            realization
            program
            returnedTrue)

  ; Opposite.satGivesTrueRun =
      λ program satisfiable →
        exactBudgetToTrueRun
          realization
          program
          (CookLevin.cookSatisfiableToExactBudgetRun
            (stateCoverage (concrete realization))
            (symbolCoverage (concrete realization))
            (nonemptyRules (concrete realization))
            (encodeProgram (concrete realization) program)
            (exactSteps (concrete realization) program)
            satisfiable)
  }

concreteRealizationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  ConcreteOppositeInterpreterRealization code →
  Direct.SATDecisionFailure candidate
concreteRealizationGivesDecisionFailure code realization =
  Opposite.semanticQuotationGivesDecisionFailure
    code
    (concreteRealizationToSemanticQuotation realization)

------------------------------------------------------------------------
-- Universal producer surface.
------------------------------------------------------------------------

record ConcreteOppositeInterpreterProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₃ where
  field
    candidateCode :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Actual.CandidateCodeRealization candidate

    realization :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      ConcreteOppositeInterpreterRealization
        (candidateCode candidate)

open ConcreteOppositeInterpreterProducer public

concreteProducerGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  ConcreteOppositeInterpreterProducer cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
concreteProducerGivesUniversalFailure producer candidate =
  concreteRealizationGivesDecisionFailure
    (candidateCode producer candidate)
    (realization producer candidate)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Cook--Levin semantic quotation itself is no longer open. The exact wall is
-- now a concrete EXECUTION REALIZATION theorem:
--
--   finite opposite interpreter
--      -> ConcreteTapeMachine + input encoder + exact budget
--      -> accepting run iff abstract run returns true.
--
-- Once that is constructed for each executable SAT candidate, the existing
-- concrete Cook--Levin theorem and finite recursion theorem close the logical
-- diagonal automatically.
------------------------------------------------------------------------
