module DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupTransitionExact where

------------------------------------------------------------------------
-- OPERATIONAL SEMANTICS OF THE COMPILED FIXED-BITSTREAM LOOKUP MACHINE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact as Link
import DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact as Cursor
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupExact as Lookup
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

linkAppendLeftOccurs :
  ∀ {State Symbol : Set}
    {rule : Local.TapeRule State Symbol}
    {left right : List (Local.TapeRule State Symbol)} →
  Local.RuleOccurs rule left →
  Local.RuleOccurs rule (Link.append left right)
linkAppendLeftOccurs Local.ruleHere = Local.ruleHere
linkAppendLeftOccurs (Local.ruleThere occurs) =
  Local.ruleThere (linkAppendLeftOccurs occurs)

linkAppendRightOccurs :
  ∀ {State Symbol : Set}
    {rule : Local.TapeRule State Symbol}
    (left : List (Local.TapeRule State Symbol))
    {right : List (Local.TapeRule State Symbol)} →
  Local.RuleOccurs rule right →
  Local.RuleOccurs rule (Link.append left right)
linkAppendRightOccurs [] occurs = occurs
linkAppendRightOccurs (x ∷ left) occurs =
  Local.ruleThere (linkAppendRightOccurs left occurs)

validStopOccursInLookup :
  ∀ {n : Nat}
    (bits : Fin.Fin n → Bool)
    (phase : Fin.Fin n) →
  Local.RuleOccurs
    (Lookup.stopRule n bits (Lookup.valid phase))
    (Coded.rules (Lookup.lookupCode n bits))
validStopOccursInLookup {n} bits phase =
  linkAppendRightOccurs
    (Mode.rules (Lookup.baseFragment n))
    (Lookup.validStopRuleOccurs bits phase)

overflowStopOccursInLookup :
  ∀ {n : Nat}
    (bits : Fin.Fin n → Bool) →
  Local.RuleOccurs
    (Lookup.stopRule n bits Lookup.overflow)
    (Coded.rules (Lookup.lookupCode n bits))
overflowStopOccursInLookup {n} bits =
  linkAppendRightOccurs
    (Mode.rules (Lookup.baseFragment n))
    (Lookup.overflowStopRuleOccurs bits)

cursorMoreOccursInBase :
  ∀ {n : Nat}
    (phase : Fin.Fin n) →
  Local.RuleOccurs
    (Mode.mapStateRule
      Mode.embedLeft
      (Phase.liftRuleAt phase Cursor.cursorRule))
    (Mode.rules (Lookup.baseFragment n))
cursorMoreOccursInBase {n} phase =
  Phase.appendLeftRuleOccurs
    (Mode.mapRuleOccurs
      (Phase.phaseLiftRuleOccurs
        Cursor.cursorSourceCode phase Local.ruleHere))

cursorMoreOccursInLookup :
  ∀ {n : Nat}
    (bits : Fin.Fin n → Bool)
    (phase : Fin.Fin n) →
  Local.RuleOccurs
    (Mode.mapStateRule
      Mode.embedLeft
      (Phase.liftRuleAt phase Cursor.cursorRule))
    (Coded.rules (Lookup.lookupCode n bits))
cursorMoreOccursInLookup {n} bits phase =
  linkAppendLeftOccurs (cursorMoreOccursInBase phase)

validMoreTransition :
  ∀ {n : Nat}
    (bits : Fin.Fin n → Bool)
    (phase : Fin.Fin n) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Lookup.lookupCode n bits)))
    (Lookup.cursorInBase n (Phase.raisePhase phase))
    Cursor.moreSymbol
  ≡
  just
    (Standard.standard-transition
      (Lookup.cursorInBase n (Fin.suc phase))
      Cursor.moreSymbol
      Local.moveRight)
validMoreTransition {n} bits phase
  with Standard.listedRuleDeterminesStandardTransition
    (Presented.finitePresentedStandardToConcrete_dispatchUnique
      (Coded.decodeCodedStandardTM (Lookup.lookupCode n bits)))
    (cursorMoreOccursInLookup bits phase)
    refl refl
... | matched , fetchExact , transitionExact = transitionExact

validStopTransition :
  ∀ {n : Nat}
    (bits : Fin.Fin n → Bool)
    (phase : Fin.Fin n) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Lookup.lookupCode n bits)))
    (Lookup.cursorInBase n (Phase.raisePhase phase))
    Cursor.stopSymbol
  ≡
  just
    (Standard.standard-transition
      (Lookup.bitSink n (bits phase))
      Cursor.stopSymbol
      Local.stayPut)
validStopTransition {n} bits phase
  with Standard.listedRuleDeterminesStandardTransition
    (Presented.finitePresentedStandardToConcrete_dispatchUnique
      (Coded.decodeCodedStandardTM (Lookup.lookupCode n bits)))
    (validStopOccursInLookup bits phase)
    refl refl
... | matched , fetchExact , transitionExact = transitionExact

overflowStopTransition :
  ∀ {n : Nat}
    (bits : Fin.Fin n → Bool) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (Lookup.lookupCode n bits)))
    (Lookup.cursorInBase n (Phase.lastPhase n))
    Cursor.stopSymbol
  ≡
  just
    (Standard.standard-transition
      (Lookup.noneSink n)
      Cursor.stopSymbol
      Local.stayPut)
overflowStopTransition {n} bits
  with Standard.listedRuleDeterminesStandardTransition
    (Presented.finitePresentedStandardToConcrete_dispatchUnique
      (Coded.decodeCodedStandardTM (Lookup.lookupCode n bits)))
    (overflowStopOccursInLookup bits)
    refl refl
... | matched , fetchExact , transitionExact = transitionExact

trueSinkIsAccepting :
  (n : Nat) → (bits : Fin.Fin n → Bool) →
  Lookup.trueSink n ≡ Coded.acceptingState (Lookup.lookupCode n bits)
trueSinkIsAccepting n bits = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- more : phase k -> k+1, one standard edge;
-- stop at k<n -> sink(bits k), one standard edge;
-- stop at overflow -> none, one standard edge.
------------------------------------------------------------------------
