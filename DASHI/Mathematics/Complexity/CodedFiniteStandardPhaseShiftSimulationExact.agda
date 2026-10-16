module DASHI.Mathematics.Complexity.CodedFiniteStandardPhaseShiftSimulationExact where

------------------------------------------------------------------------
-- SHIFT A T-PHASE WRAPPER INTO PHASES 1..T+1 OF THE (T+1)-WRAPPER
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Fin.Base as Fin
open import Data.Fin.Properties using (remQuot-combine)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural

------------------------------------------------------------------------
-- Decode (q,phase), increment phase, re-encode.
------------------------------------------------------------------------

shiftPhaseState :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Fin.Fin (Coded.stateCount source * suc steps) →
  Fin.Fin (Coded.stateCount source * suc (suc steps))
shiftPhaseState source steps code =
  Fin.combine
    (proj₁ split)
    (Fin.suc (proj₂ split))
  where
    split =
      Fin.remQuot {m = Coded.stateCount source} (suc steps) code

shiftPhaseStateCombined :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  (q : Fin.Fin (Coded.stateCount source)) →
  (phase : Fin.Fin (suc steps)) →
  shiftPhaseState source steps (Fin.combine q phase)
    ≡ Fin.combine q (Fin.suc phase)
shiftPhaseStateCombined source steps q phase
  rewrite remQuot-combine
    {n = Coded.stateCount source} {k = suc steps} q phase = refl

------------------------------------------------------------------------
-- A copied rule at phase k maps to the copied rule at phase suc k.
------------------------------------------------------------------------

shiftLiftRuleExact :
  ∀ {steps : Nat}
    (source : Coded.CodedFiniteStandardTM)
    (phase : Fin.Fin steps)
    (rule : Local.TapeRule
      (Fin.Fin (Coded.stateCount source))
      (Fin.Fin (Coded.symbolCount source))) →
  Mode.mapStateRule
      (shiftPhaseState source steps)
      (Phase.liftRuleAt phase rule)
    ≡ Phase.liftRuleAt (Fin.suc phase) rule
shiftLiftRuleExact {steps} source phase rule
  rewrite shiftPhaseStateCombined
            source steps (Local.sourceState rule) (Phase.raisePhase phase)
        | shiftPhaseStateCombined
            source steps (Local.targetState rule) (Fin.suc phase) = refl

------------------------------------------------------------------------
-- Every fetched rule of the smaller wrapper is present after phase shift.
------------------------------------------------------------------------

shiftFetchedRuleOccurs :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM}
    {q : Fin.Fin (Coded.stateCount source * suc steps)}
    {a : Fin.Fin (Coded.symbolCount source)}
    (matched : Interpreter.MatchedRule
      (Phase.phaseLiftConcreteMachine source steps)
      q a
      (Phase.phaseLiftRules source steps)) →
  Local.RuleOccurs
    (Mode.mapStateRule
      (shiftPhaseState source steps)
      (Interpreter.rule matched))
    (Phase.phaseLiftRules source (suc steps))
shiftFetchedRuleOccurs {steps} {source} matched
  with Phase.phaseTablePreimage
    (Coded.allFin steps)
    (Interpreter.occurs matched)
... | phase , original , originalOccurs , exact
  rewrite exact
        | shiftLiftRuleExact source phase original =
  Phase.phaseLiftRuleOccurs source (Fin.suc phase) originalOccurs

------------------------------------------------------------------------
-- Target transition selected in the larger wrapper.
------------------------------------------------------------------------

shiftFetchedRuleTargetTransition :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM}
    {q : Fin.Fin (Coded.stateCount source * suc steps)}
    {a : Fin.Fin (Coded.symbolCount source)}
    (matched : Interpreter.MatchedRule
      (Phase.phaseLiftConcreteMachine source steps)
      q a
      (Phase.phaseLiftRules source steps)) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM
        (Phase.phaseLiftCode source (suc steps))))
    (shiftPhaseState source steps q)
    a
  ≡
  just
    (Standard.standard-transition
      (shiftPhaseState source steps
        (Local.targetState (Interpreter.rule matched)))
      (Local.writeSymbol (Interpreter.rule matched))
      (Local.direction (Interpreter.rule matched)))
shiftFetchedRuleTargetTransition {steps} {source} matched
  rewrite sym (Interpreter.sourceExact matched)
        | sym (Interpreter.readExact matched)
  with Standard.listedRuleDeterminesStandardTransition
    (Phase.phaseLiftConcreteDeterministic source (suc steps))
    (shiftFetchedRuleOccurs matched)
    refl
    refl
... | targetMatched , fetchExact , transitionExact = transitionExact

------------------------------------------------------------------------
-- Ordinary tape update commutes with the state-only phase shift.
------------------------------------------------------------------------

applyTransitionCommutes :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM}
    (before : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps))))
    (selected : Standard.StandardTransition
      (Fin.Fin (Coded.stateCount source * suc steps))
      (Fin.Fin (Coded.symbolCount source))) →
  Standard.standardApplyTransition
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source (suc steps))))
      (Structural.structuralEmbed
        (shiftPhaseState source steps)
        (λ symbol → symbol)
        before)
      (Standard.standard-transition
        (shiftPhaseState source steps (Standard.targetState selected))
        (Standard.writeSymbol selected)
        (Standard.direction selected))
  ≡
  Structural.structuralEmbed
    (shiftPhaseState source steps)
    (λ symbol → symbol)
    (Standard.standardApplyTransition
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
      before selected)
applyTransitionCommutes
    (Standard.standard-configuration [] q a rightTape)
    (Standard.standard-transition q' b Local.moveLeft) = refl
applyTransitionCommutes
    (Standard.standard-configuration (l ∷ leftTape) q a rightTape)
    (Standard.standard-transition q' b Local.moveLeft) = refl
applyTransitionCommutes
    (Standard.standard-configuration leftTape q a rightTape)
    (Standard.standard-transition q' b Local.stayPut) = refl
applyTransitionCommutes
    (Standard.standard-configuration leftTape q a [])
    (Standard.standard-transition q' b Local.moveRight) = refl
applyTransitionCommutes
    (Standard.standard-configuration leftTape q a (r ∷ rightTape))
    (Standard.standard-transition q' b Local.moveRight) = refl

justInjective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

shiftStepExact :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM}
    {before after : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))} →
  Standard.standardNext
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
      before
    ≡ just after →
  Standard.standardNext
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source (suc steps))))
      (Structural.structuralEmbed
        (shiftPhaseState source steps)
        (λ symbol → symbol)
        before)
    ≡
    just
      (Structural.structuralEmbed
        (shiftPhaseState source steps)
        (λ symbol → symbol)
        after)
shiftStepExact {steps} {source} {before} {after} sourceNext
  with Interpreter.fetchConcreteRule
    (Phase.phaseLiftConcreteMachine source steps)
    (Standard.state before)
    (Standard.scanned before)
... | nothing
  with sourceNext
... | ()
... | just matched
  rewrite shiftFetchedRuleTargetTransition matched =
  cong just
    (trans
      (applyTransitionCommutes before (Standard.matchedRuleTransition matched))
      (cong
        (Structural.structuralEmbed
          (shiftPhaseState source steps)
          (λ symbol → symbol))
        (justInjective sourceNext)))

phaseShiftStructuralSimulation :
  ∀ {steps : Nat}
    {source : Coded.CodedFiniteStandardTM} →
  Structural.StructuralStandardMachineSimulation
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source steps)))
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Phase.phaseLiftCode source (suc steps))))
phaseShiftStructuralSimulation {steps} {source} = record
  { Structural.stateMap = shiftPhaseState source steps
  ; Structural.symbolMap = λ symbol → symbol
  ; Structural.symbolMapInjective = λ equality → equality
  ; Structural.blankExact = refl
  ; Structural.stepExact = shiftStepExact
  }

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- A recursively constructed T-step phase-lifted run can be reused verbatim as
-- phases 1..T+1 of the next wrapper.  The embedding preserves tape symbols and
-- one source edge remains exactly one target edge.
------------------------------------------------------------------------
