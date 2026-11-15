module DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseRunExact where

------------------------------------------------------------------------
-- WHOLE-RUN LIFT THROUGH THE EXACT FINITE-CONTROL PHASE WRAPPER
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase
import DASHI.Mathematics.Complexity.CodedFiniteStandardPhaseShiftSimulationExact as Shift
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Simulation
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural

sourceStandard :
  Coded.CodedFiniteStandardTM → Set
sourceStandard source =
  Standard.StandardConfiguration
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM source))

------------------------------------------------------------------------
-- Direct embedding of one source configuration at one elapsed phase.
------------------------------------------------------------------------

phaseEmbedAt :
  ∀ {steps : Nat}
    (source : Coded.CodedFiniteStandardTM) →
  Fin.Fin (suc steps) →
  Standard.StandardConfiguration
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM source)) →
  Standard.StandardConfiguration
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
phaseEmbedAt source phase configuration =
  Standard.standard-configuration
    (Standard.left configuration)
    (Phase.phaseState (Standard.state configuration) phase)
    (Standard.scanned configuration)
    (Standard.right configuration)

------------------------------------------------------------------------
-- One source transition copied at one nonterminal phase.
------------------------------------------------------------------------

phaseApplyTransitionCommutes :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM}
    (phase : Fin.Fin steps)
    (before : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source)))
    (selected : Standard.StandardTransition
      (Fin.Fin (Coded.stateCount source))
      (Fin.Fin (Coded.symbolCount source))) →
  Standard.standardApplyTransition
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
      (phaseEmbedAt source (Phase.raisePhase phase) before)
      (Standard.standard-transition
        (Phase.phaseTargetState source (Standard.targetState selected) phase)
        (Standard.writeSymbol selected)
        (Standard.direction selected))
  ≡
  phaseEmbedAt source (Fin.suc phase)
    (Standard.standardApplyTransition
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source))
      before selected)
phaseApplyTransitionCommutes phase
    (Standard.standard-configuration [] q a rightTape)
    (Standard.standard-transition q' b Local.moveLeft) = refl
phaseApplyTransitionCommutes phase
    (Standard.standard-configuration (l ∷ leftTape) q a rightTape)
    (Standard.standard-transition q' b Local.moveLeft) = refl
phaseApplyTransitionCommutes phase
    (Standard.standard-configuration leftTape q a rightTape)
    (Standard.standard-transition q' b Local.stayPut) = refl
phaseApplyTransitionCommutes phase
    (Standard.standard-configuration leftTape q a [])
    (Standard.standard-transition q' b Local.moveRight) = refl
phaseApplyTransitionCommutes phase
    (Standard.standard-configuration leftTape q a (r ∷ rightTape))
    (Standard.standard-transition q' b Local.moveRight) = refl

phaseFetchedRuleTargetTransition :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM}
    (phase : Fin.Fin steps)
    {q : Fin.Fin (Coded.stateCount source)}
    {a : Fin.Fin (Coded.symbolCount source)}
    (matched : Interpreter.MatchedRule
      (Presented.finitePresentedStandardToConcrete
        (Coded.decodeCodedStandardTM source))
      q a
      (Coded.rules source)) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
    (Phase.phaseSourceState source q phase)
    a
  ≡
  just
    (Standard.standard-transition
      (Phase.phaseTargetState source
        (Local.targetState (Interpreter.rule matched)) phase)
      (Local.writeSymbol (Interpreter.rule matched))
      (Local.direction (Interpreter.rule matched)))
phaseFetchedRuleTargetTransition {source = source} phase matched
  rewrite sym (Interpreter.sourceExact matched)
        | sym (Interpreter.readExact matched)
  with Phase.phaseLiftListedRuleDeterminesStandardTransition
    source phase (Interpreter.occurs matched)
... | targetMatched , fetchExact , transitionExact = transitionExact

justInjective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

phaseStepExact :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM}
    (phase : Fin.Fin steps)
    {before after : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source))} →
  Standard.standardNext
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source))
      before
    ≡ just after →
  Standard.standardNext
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
      (phaseEmbedAt source (Phase.raisePhase phase) before)
    ≡ just (phaseEmbedAt source (Fin.suc phase) after)
phaseStepExact {source = source} phase {before} {after} sourceNext
  with Interpreter.fetchConcreteRule
    (Presented.finitePresentedStandardToConcrete
      (Coded.decodeCodedStandardTM source))
    (Standard.state before)
    (Standard.scanned before)
... | nothing
  with sourceNext
... | ()
... | just matched
  rewrite phaseFetchedRuleTargetTransition phase matched =
  cong just
    (trans
      (phaseApplyTransitionCommutes
        phase before (Standard.matchedRuleTransition matched))
      (cong
        (phaseEmbedAt source (Fin.suc phase))
        (justInjective sourceNext)))

------------------------------------------------------------------------
-- Normalise the recursive phase-shifted endpoints.
------------------------------------------------------------------------

mapIdentity : ∀ {A : Set} (xs : List A) → Structural.mapList (λ x → x) xs ≡ xs
mapIdentity [] = refl
mapIdentity (x ∷ xs)
  rewrite mapIdentity xs = refl

shiftPhaseEmbedExact :
  ∀ {steps : Nat}
    (source : Coded.CodedFiniteStandardTM)
    (phase : Fin.Fin (suc steps))
    (configuration : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source))) →
  Structural.structuralEmbed
      (Shift.shiftPhaseState source steps)
      (λ symbol → symbol)
      (phaseEmbedAt source phase configuration)
  ≡
  phaseEmbedAt source (Fin.suc phase) configuration
shiftPhaseEmbedExact source phase
    (Standard.standard-configuration left q a right)
  rewrite mapIdentity left
        | mapIdentity right
        | Shift.shiftPhaseStateCombined source _ q phase = refl

transportRunEndpoints :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {steps : Nat}
    {oldStart oldFinish newStart newFinish : Standard.StandardConfiguration machine} →
  oldStart ≡ newStart →
  oldFinish ≡ newFinish →
  Run.StandardExactRun machine steps oldStart oldFinish →
  Run.StandardExactRun machine steps newStart newFinish
transportRunEndpoints refl refl run = run

shiftRecursiveTail :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM}
    {start finish : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source))} →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
    steps
    (phaseEmbedAt source Fin.zero start)
    (phaseEmbedAt source (Phase.lastPhase steps) finish) →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source (suc steps))))
    steps
    (phaseEmbedAt source (Fin.suc Fin.zero) start)
    (phaseEmbedAt source (Phase.lastPhase (suc steps)) finish)
shiftRecursiveTail {steps} {source} {start} {finish} run =
  transportRunEndpoints
    (shiftPhaseEmbedExact source Fin.zero start)
    (shiftPhaseEmbedExact source (Phase.lastPhase steps) finish)
    (Simulation.simulateExactRun
      (Structural.structuralToSimulation
        (Shift.phaseShiftStructuralSimulation {steps = steps} {source = source}))
      run)

------------------------------------------------------------------------
-- Main theorem: same T source edges -> same T phase-lifted edges.
------------------------------------------------------------------------

phaseLiftExactRun :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {steps : Nat}
    {start finish : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source))} →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM source))
    steps start finish →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
    steps
    (phaseEmbedAt source Fin.zero start)
    (phaseEmbedAt source (Phase.lastPhase steps) finish)
phaseLiftExactRun Run.standardRunDone = Run.standardRunDone
phaseLiftExactRun
    {source = source}
    (Run.standardRunStep {steps = steps} {current = current} {next = next} edge rest) =
  Run.standardRunStep
    (phaseStepExact {source = source} Fin.zero edge)
    (shiftRecursiveTail (phaseLiftExactRun rest))

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The exact-T phase wrapper is now semantically transparent: it preserves the
-- source tape evolution edge-for-edge, adds only a finite elapsed-phase control
-- coordinate, and ends after exactly T source edges in the syntactically
-- quiescent terminal slice.  A return/opposite link can therefore leave the
-- terminal configuration without overriding any resident candidate transition.
------------------------------------------------------------------------
