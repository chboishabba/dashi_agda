module DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedRunSimulationExact where

------------------------------------------------------------------------
-- EXACT WHOLE-RUN LIFT INTO A SUMMED + SAFELY LINKED CODED TARGET
--
-- The linked structural owner already proves one-step commutation for the
-- actual resident source rule table.  The generic simulation owner already
-- proves that step preservation lifts to exact runs with IDENTICAL step count.
-- This module composes those two paid facts and then specializes them to the
-- literal execution witness carried by CodedStandardPolynomialDecider.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact as Link
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedStructuralSimulationExact as Linked
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as CodedDecider
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Simulation
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

------------------------------------------------------------------------
-- The linked one-step simulation viewed through the generic exact-run API.
------------------------------------------------------------------------

linkedStandardSimulation :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)} →
  (extension : Link.SafeLinkExtension (Linked.baseCombined source right)) →
  Simulation.StandardMachineSimulation
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM source))
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM
        (Linked.linkedTargetCode source right extension)))
linkedStandardSimulation extension =
  Structural.structuralToSimulation
    (Linked.linkedStructuralSimulation extension)

------------------------------------------------------------------------
-- Exact whole-run preservation.  There is no extra transition factor here:
-- every source edge is one target edge inside the resident candidate mode.
------------------------------------------------------------------------

simulateLinkedExactRun :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    (extension : Link.SafeLinkExtension (Linked.baseCombined source right))
    {steps : Nat}
    {start finish :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM source))} →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM source))
    steps start finish →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM
        (Linked.linkedTargetCode source right extension)))
    steps
    (Structural.structuralEmbed
      (Linked.sourceStateMap source right)
      (λ symbol → symbol)
      start)
    (Structural.structuralEmbed
      (Linked.sourceStateMap source right)
      (λ symbol → symbol)
      finish)
simulateLinkedExactRun extension run =
  Simulation.simulateExactRun
    (linkedStandardSimulation extension)
    run

------------------------------------------------------------------------
-- Specialization to the ACTUAL polynomial candidate execution witness.
------------------------------------------------------------------------

simulateCodedCandidateExecution :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : CodedDecider.CodedStandardPolynomialDecider decider)
    (right : Mode.CodedModeFragment
      (Coded.symbolCount (CodedDecider.code witness)))
    (extension : Link.SafeLinkExtension
      (Linked.baseCombined (CodedDecider.code witness) right))
    (formula : Cook.BooleanFormula) →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM
        (Linked.linkedTargetCode
          (CodedDecider.code witness) right extension)))
    (CodedDecider.polynomialStepBudget
      (CodedDecider.clockCoefficient witness)
      (CodedDecider.clockDegree witness)
      formula)
    (Structural.structuralEmbed
      (Linked.sourceStateMap (CodedDecider.code witness) right)
      (λ symbol → symbol)
      (Language.guardedStandardStart
        (CodedDecider.formulaInput
          (CodedDecider.code witness)
          (CodedDecider.zeroSymbol witness)
          (CodedDecider.oneSymbol witness)
          formula)
        (CodedDecider.polynomialStepBudget
          (CodedDecider.clockCoefficient witness)
          (CodedDecider.clockDegree witness)
          formula)))
    (Structural.structuralEmbed
      (Linked.sourceStateMap (CodedDecider.code witness) right)
      (λ symbol → symbol)
      (CodedDecider.finish witness formula))
simulateCodedCandidateExecution witness right extension formula =
  simulateLinkedExactRun extension
    (CodedDecider.execution witness formula)

------------------------------------------------------------------------
-- Endpoint control is definitionally the disjoint left-mode injection of the
-- source candidate's endpoint control.  Downstream opposite-suffix code can use
-- this equality when wiring a return link without reopening candidate semantics.
------------------------------------------------------------------------

linkedCandidateFinishStateExact :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : CodedDecider.CodedStandardPolynomialDecider decider)
    (right : Mode.CodedModeFragment
      (Coded.symbolCount (CodedDecider.code witness)))
    (formula : Cook.BooleanFormula) →
  Standard.state
    (Structural.structuralEmbed
      (Linked.sourceStateMap (CodedDecider.code witness) right)
      (λ symbol → symbol)
      (CodedDecider.finish witness formula))
  ≡
  Linked.sourceStateMap
    (CodedDecider.code witness)
    right
    (Standard.state (CodedDecider.finish witness formula))
linkedCandidateFinishStateExact witness right formula = refl

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- Wall C no longer contains the candidate middle run itself.  Once generator
-- call/return links place the target in the embedded candidate start state, the
-- ACTUAL polynomial candidate run transports edge-for-edge through the linked
-- target with exactly the original polynomial step count.  Remaining C-work is
-- generator call/return execution plus composition with this paid middle run;
-- candidate simulation and its clock are not separate obligations anymore.
------------------------------------------------------------------------
