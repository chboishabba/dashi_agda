module DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedStructuralSimulationExact where

------------------------------------------------------------------------
-- ACTUAL STRUCTURAL SIMULATION INTO A SUMMED + SAFELY LINKED CODED TARGET
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact as Link
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkTransitionPreservationExact as LinkPres
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeTransitionEmbeddingExact as EmbedRule
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural

baseCombined :
  (source : Coded.CodedFiniteStandardTM) →
  Mode.CodedModeFragment (Coded.symbolCount source) →
  Mode.CodedModeFragment (Coded.symbolCount source)
baseCombined source right =
  Mode.sumFragments (Mode.fragmentFromCode source) right

sourceStateMap :
  ∀ (source : Coded.CodedFiniteStandardTM)
    (right : Mode.CodedModeFragment (Coded.symbolCount source)) →
  Fin.Fin (Coded.stateCount source) →
  Fin.Fin (Mode.stateCount (baseCombined source right))
sourceStateMap source right =
  Mode.embedLeft {Coded.stateCount source} {Mode.stateCount right}

linkedTargetCode :
  ∀ (source : Coded.CodedFiniteStandardTM)
    (right : Mode.CodedModeFragment (Coded.symbolCount source)) →
  Link.SafeLinkExtension (baseCombined source right) →
  Coded.CodedFiniteStandardTM
linkedTargetCode source right extension =
  Mode.closeFragment
    (Link.extendFragmentWithLinks extension)
    (Coded.blank source)
    (sourceStateMap source right (Coded.initialState source))
    (sourceStateMap source right (Coded.acceptingState source))

------------------------------------------------------------------------
-- The ordinary split-tape transition application commutes with the state-only
-- embedding and identity symbol map.
------------------------------------------------------------------------

applyTransitionCommutes :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    {extension : Link.SafeLinkExtension (baseCombined source right)}
    (before : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source)))
    (selected : Standard.StandardTransition
      (Fin.Fin (Coded.stateCount source))
      (Fin.Fin (Coded.symbolCount source))) →
  Standard.standardApplyTransition
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (linkedTargetCode source right extension)))
      (Structural.structuralEmbed
        (sourceStateMap source right)
        (λ symbol → symbol)
        before)
      (Standard.standard-transition
        (sourceStateMap source right (Standard.targetState selected))
        (Standard.writeSymbol selected)
        (Standard.direction selected))
  ≡
  Structural.structuralEmbed
    (sourceStateMap source right)
    (λ symbol → symbol)
    (Standard.standardApplyTransition
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM source))
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

------------------------------------------------------------------------
-- The fetched source rule occurs in the resident left mode before links.
------------------------------------------------------------------------

mappedFetchedRuleResidentOccurs :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    {q : Fin.Fin (Coded.stateCount source)}
    {a : Fin.Fin (Coded.symbolCount source)}
    (matched : Interpreter.MatchedRule
      (Presented.finitePresentedStandardToConcrete
        (Coded.decodeCodedStandardTM source))
      q a
      (Coded.rules source)) →
  Local.RuleOccurs
    (Mode.mapStateRule
      (sourceStateMap source right)
      (Interpreter.rule matched))
    (Mode.rules (baseCombined source right))
mappedFetchedRuleResidentOccurs {source} {right} matched =
  EmbedRule.leftOccursInAppend
    (Mode.mapRuleOccurs (Interpreter.occurs matched))

mappedFetchedRuleTargetTransition :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    (extension : Link.SafeLinkExtension (baseCombined source right))
    {q : Fin.Fin (Coded.stateCount source)}
    {a : Fin.Fin (Coded.symbolCount source)}
    (matched : Interpreter.MatchedRule
      (Presented.finitePresentedStandardToConcrete
        (Coded.decodeCodedStandardTM source))
      q a
      (Coded.rules source)) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (linkedTargetCode source right extension)))
    (sourceStateMap source right q)
    a
  ≡
  just
    (Standard.standard-transition
      (sourceStateMap source right
        (Local.targetState (Interpreter.rule matched)))
      (Local.writeSymbol (Interpreter.rule matched))
      (Local.direction (Interpreter.rule matched)))
mappedFetchedRuleTargetTransition {source} {right} extension matched
  rewrite sym (Interpreter.sourceExact matched)
        | sym (Interpreter.readExact matched) =
  LinkPres.residentRuleDeterminesExtendedTransition
    extension
    (Coded.blank source)
    (sourceStateMap source right (Coded.initialState source))
    (sourceStateMap source right (Coded.acceptingState source))
    (mappedFetchedRuleResidentOccurs matched)

------------------------------------------------------------------------
-- Full `standardNext` preservation.
------------------------------------------------------------------------

linkedStepExact :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    (extension : Link.SafeLinkExtension (baseCombined source right))
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
        (Coded.decodeCodedStandardTM (linkedTargetCode source right extension)))
      (Structural.structuralEmbed
        (sourceStateMap source right)
        (λ symbol → symbol)
        before)
    ≡
    just
      (Structural.structuralEmbed
        (sourceStateMap source right)
        (λ symbol → symbol)
        after)
linkedStepExact {source} {right} extension {before} {after} sourceNext
  with Interpreter.fetchConcreteRule
    (Presented.finitePresentedStandardToConcrete
      (Coded.decodeCodedStandardTM source))
    (Standard.state before)
    (Standard.scanned before)
... | nothing
  with sourceNext
... | ()
... | just matched
  rewrite mappedFetchedRuleTargetTransition extension matched =
  cong just
    (trans
      (applyTransitionCommutes
        before
        (Standard.matchedRuleTransition matched))
      (cong
        (Structural.structuralEmbed
          (sourceStateMap source right)
          (λ symbol → symbol))
        (justInjective sourceNext)))
  where
    justInjective :
      ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
    justInjective refl = refl

------------------------------------------------------------------------
-- Inhabitant of the existing structural simulation interface.
------------------------------------------------------------------------

linkedStructuralSimulation :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)} →
  (extension : Link.SafeLinkExtension (baseCombined source right)) →
  Structural.StructuralStandardMachineSimulation
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM source))
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (linkedTargetCode source right extension)))
linkedStructuralSimulation {source} {right} extension = record
  { Structural.stateMap = sourceStateMap source right
  ; Structural.symbolMap = λ symbol → symbol
  ; Structural.symbolMapInjective = λ equality → equality
  ; Structural.blankExact = refl
  ; Structural.stepExact = linkedStepExact extension
  }

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The candidate middle phase can now be embedded into a larger literal coded
-- machine by theorem, not by an arbitrary meta-level `embed`: source states are
-- a disjoint Fin region, symbols are unchanged, every actual fetched rule is
-- preserved through safe links, and whole `standardNext` steps commute.
------------------------------------------------------------------------
