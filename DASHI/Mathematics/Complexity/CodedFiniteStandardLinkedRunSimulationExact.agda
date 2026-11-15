module DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedRunSimulationExact where

------------------------------------------------------------------------
-- EXACT WHOLE-RUN LIFT INTO A SUMMED + SAFELY LINKED CODED TARGET
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

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
-- Prefix ; source candidate ; suffix composition on the SAME linked target.
-- The middle run is generated automatically from the source run, so callers
-- supply only the surrounding target-mode runs.
------------------------------------------------------------------------

appendLinkedCandidatePhase :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    (extension : Link.SafeLinkExtension (Linked.baseCombined source right))
    {prefixSteps candidateSteps suffixSteps : Nat}
    {sourceStart sourceFinish :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM source))}
    {targetStart targetFinish :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM
            (Linked.linkedTargetCode source right extension)))} →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM
        (Linked.linkedTargetCode source right extension)))
    prefixSteps
    targetStart
    (Structural.structuralEmbed
      (Linked.sourceStateMap source right)
      (λ symbol → symbol)
      sourceStart) →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM source))
    candidateSteps sourceStart sourceFinish →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM
        (Linked.linkedTargetCode source right extension)))
    suffixSteps
    (Structural.structuralEmbed
      (Linked.sourceStateMap source right)
      (λ symbol → symbol)
      sourceFinish)
    targetFinish →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM
        (Linked.linkedTargetCode source right extension)))
    ((prefixSteps + candidateSteps) + suffixSteps)
    targetStart targetFinish
appendLinkedCandidatePhase extension prefix candidate suffix =
  Simulation.appendThreeExactRuns
    prefix
    (simulateLinkedExactRun extension candidate)
    suffix

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
-- Wall C no longer contains either the candidate middle run OR phase
-- composition.  Once a generator/call prefix reaches the embedded candidate
-- start and a return/opposite suffix starts at the embedded candidate finish,
-- `appendLinkedCandidatePhase` produces the complete exact target run with the
-- literal additive clock.  Remaining C-work is therefore construction of those
-- surrounding runs and their boundary configurations only.
------------------------------------------------------------------------
