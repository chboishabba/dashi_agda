module DASHI.Mathematics.Complexity.CodedFiniteStandardModeTransitionEmbeddingExact where

------------------------------------------------------------------------
-- SOURCE RULES REMAIN THE SAME STANDARD TRANSITIONS INSIDE A MODE SUM
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Data.Product using (Σ; _,_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented

------------------------------------------------------------------------
-- A source code plus any same-alphabet fragment, closed with source blank and
-- embedded source endpoints.
------------------------------------------------------------------------

combinedWithRight :
  (source : Coded.CodedFiniteStandardTM) →
  Mode.CodedModeFragment (Coded.symbolCount source) →
  Coded.CodedFiniteStandardTM
combinedWithRight source right =
  Mode.closeFragment
    combined
    (Coded.blank source)
    (Mode.embedLeft
      {Coded.stateCount source}
      {Mode.stateCount right}
      (Coded.initialState source))
    (Mode.embedLeft
      {Coded.stateCount source}
      {Mode.stateCount right}
      (Coded.acceptingState source))
  where
    combined : Mode.CodedModeFragment (Coded.symbolCount source)
    combined =
      Mode.sumFragments (Mode.fragmentFromCode source) right

leftOccursInAppend :
  ∀ {State Symbol : Set}
    {rule : Local.TapeRule State Symbol}
    {left right : List (Local.TapeRule State Symbol)} →
  Local.RuleOccurs rule left →
  Local.RuleOccurs rule (Mode.append left right)
leftOccursInAppend Local.ruleHere = Local.ruleHere
leftOccursInAppend (Local.ruleThere occurs) =
  Local.ruleThere (leftOccursInAppend occurs)

embeddedSourceRuleOccurs :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    {rule : Local.TapeRule
      (Fin.Fin (Coded.stateCount source))
      (Fin.Fin (Coded.symbolCount source))} →
  Local.RuleOccurs rule (Coded.rules source) →
  Local.RuleOccurs
    (Mode.mapStateRule
      (Mode.embedLeft
        {Coded.stateCount source}
        {Mode.stateCount right})
      rule)
    (Coded.rules (combinedWithRight source right))
embeddedSourceRuleOccurs {source} {right} occurs =
  leftOccursInAppend
    (Mode.mapRuleOccurs occurs)

------------------------------------------------------------------------
-- Every listed source rule determines the corresponding embedded transition in
-- the combined target.  This uses the existing exact first-match interpreter /
-- dispatch-uniqueness theorem; no transition oracle is introduced.
------------------------------------------------------------------------

embeddedListedRuleDeterminesTargetTransition :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    {rule : Local.TapeRule
      (Fin.Fin (Coded.stateCount source))
      (Fin.Fin (Coded.symbolCount source))} →
  Local.RuleOccurs rule (Coded.rules source) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (combinedWithRight source right)))
    (Mode.embedLeft
      {Coded.stateCount source}
      {Mode.stateCount right}
      (Local.sourceState rule))
    (Local.readSymbol rule)
  ≡
  just
    (Standard.standard-transition
      (Mode.embedLeft
        {Coded.stateCount source}
        {Mode.stateCount right}
        (Local.targetState rule))
      (Local.writeSymbol rule)
      (Local.direction rule))
embeddedListedRuleDeterminesTargetTransition
    {source} {right} {rule} occurs
  with Standard.listedRuleDeterminesStandardTransition
    (Presented.finitePresentedStandardToConcrete_dispatchUnique
      (Coded.decodeCodedStandardTM (combinedWithRight source right)))
    (embeddedSourceRuleOccurs {source} {right} occurs)
    refl refl
... | matched , fetchExact , transitionExact = transitionExact

------------------------------------------------------------------------
-- The same source rule determines its ordinary source transition.
------------------------------------------------------------------------

listedRuleDeterminesSourceTransition :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {rule : Local.TapeRule
      (Fin.Fin (Coded.stateCount source))
      (Fin.Fin (Coded.symbolCount source))} →
  Local.RuleOccurs rule (Coded.rules source) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM source))
    (Local.sourceState rule)
    (Local.readSymbol rule)
  ≡
  just
    (Standard.standard-transition
      (Local.targetState rule)
      (Local.writeSymbol rule)
      (Local.direction rule))
listedRuleDeterminesSourceTransition {source} {rule} occurs
  with Standard.listedRuleDeterminesStandardTransition
    (Presented.finitePresentedStandardToConcrete_dispatchUnique
      (Coded.decodeCodedStandardTM source))
    occurs refl refl
... | matched , fetchExact , transitionExact = transitionExact

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Static mode composition preserves the candidate control table rule-for-rule:
-- source control is injected by `embedLeft`, tape symbols/writes/directions are
-- unchanged, and the target transition selected by the ordinary standard
-- interpreter is exactly the embedded source transition.  Safe link extension
-- can preserve this further whenever link dispatch keys are fresh.
------------------------------------------------------------------------
