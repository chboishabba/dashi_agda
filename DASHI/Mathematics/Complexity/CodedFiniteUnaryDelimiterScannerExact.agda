module DASHI.Mathematics.Complexity.CodedFiniteUnaryDelimiterScannerExact where

------------------------------------------------------------------------
-- CONSTANT-CONTROL SCANNER FOR SELF-DELIMITING UNARY NAT FIELDS
--
-- Encoding is true^n ; false.  Unlike the phase-lift cursor, this fragment does
-- not allocate one state per n: it loops in one scan state for arbitrary n and
-- reaches a genuinely quiescent done state at the terminator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

stateCount : Nat
stateCount = 2

symbolCount : Nat
symbolCount = 3

scanState : Fin.Fin stateCount
scanState = Fin.zero

doneState : Fin.Fin stateCount
doneState = Fin.suc Fin.zero

blankSymbol : Fin.Fin symbolCount
blankSymbol = Fin.zero

trueSymbol : Fin.Fin symbolCount
trueSymbol = Fin.suc Fin.zero

falseTerminator : Fin.Fin symbolCount
falseTerminator = Fin.suc (Fin.suc Fin.zero)

scanTrueRule :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
scanTrueRule =
  Local.tape-rule
    scanState trueSymbol
    scanState trueSymbol
    Local.moveRight

finishFalseRule :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
finishFalseRule =
  Local.tape-rule
    scanState falseTerminator
    doneState falseTerminator
    Local.stayPut

scannerRules :
  Agda.Builtin.List.List
    (Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount))
scannerRules = scanTrueRule ∷ finishFalseRule ∷ []

scannerDispatchUnique :
  ∀ {left right} →
  Local.RuleOccurs left scannerRules →
  Local.RuleOccurs right scannerRules →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right
scannerDispatchUnique Local.ruleHere Local.ruleHere sourceEq readEq = refl
scannerDispatchUnique Local.ruleHere (Local.ruleThere Local.ruleHere) sourceEq ()
scannerDispatchUnique Local.ruleHere (Local.ruleThere (Local.ruleThere ())) sourceEq readEq
scannerDispatchUnique (Local.ruleThere Local.ruleHere) Local.ruleHere sourceEq ()
scannerDispatchUnique
    (Local.ruleThere Local.ruleHere)
    (Local.ruleThere Local.ruleHere)
    sourceEq readEq = refl
scannerDispatchUnique
    (Local.ruleThere Local.ruleHere)
    (Local.ruleThere (Local.ruleThere ()))
    sourceEq readEq
scannerDispatchUnique (Local.ruleThere (Local.ruleThere ())) right sourceEq readEq

scannerCode : Coded.CodedFiniteStandardTM
scannerCode = record
  { Coded.stateCount = stateCount
  ; Coded.symbolCount = symbolCount
  ; Coded.blank = blankSymbol
  ; Coded.initialState = scanState
  ; Coded.acceptingState = doneState
  ; Coded.rules = scannerRules
  ; Coded.dispatchUnique = scannerDispatchUnique
  }

scannerMachine =
  Presented.finitePresentedStandardMachine
    (Coded.decodeCodedStandardTM scannerCode)

scanTrueTransition :
  Standard.transition scannerMachine scanState trueSymbol
  ≡ just
    (Standard.standard-transition
      scanState trueSymbol Local.moveRight)
scanTrueTransition =
  transitionFromListedRule scanTrueRule Local.ruleHere refl refl
  where
    transitionFromListedRule :
      (rule : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)) →
      Local.RuleOccurs rule scannerRules →
      Local.sourceState rule ≡ scanState →
      Local.readSymbol rule ≡ trueSymbol →
      Standard.transition scannerMachine scanState trueSymbol
      ≡ just
        (Standard.standard-transition
          (Local.targetState rule)
          (Local.writeSymbol rule)
          (Local.direction rule))
    transitionFromListedRule rule occurs sourceEq readEq
      with Standard.listedRuleDeterminesStandardTransition
        (Presented.finitePresentedStandardToConcrete_dispatchUnique
          (Coded.decodeCodedStandardTM scannerCode))
        occurs sourceEq readEq
    ... | matched , fetchExact , transitionExact = transitionExact

finishFalseTransition :
  Standard.transition scannerMachine scanState falseTerminator
  ≡ just
    (Standard.standard-transition
      doneState falseTerminator Local.stayPut)
finishFalseTransition =
  transitionFromListedRule finishFalseRule
    (Local.ruleThere Local.ruleHere) refl refl
  where
    transitionFromListedRule :
      (rule : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)) →
      Local.RuleOccurs rule scannerRules →
      Local.sourceState rule ≡ scanState →
      Local.readSymbol rule ≡ falseTerminator →
      Standard.transition scannerMachine scanState falseTerminator
      ≡ just
        (Standard.standard-transition
          (Local.targetState rule)
          (Local.writeSymbol rule)
          (Local.direction rule))
    transitionFromListedRule rule occurs sourceEq readEq
      with Standard.listedRuleDeterminesStandardTransition
        (Presented.finitePresentedStandardToConcrete_dispatchUnique
          (Coded.decodeCodedStandardTM scannerCode))
        occurs sourceEq readEq
    ... | matched , fetchExact , transitionExact = transitionExact

doneStateHasNoResidentRule :
  ∀ {rule} →
  Local.RuleOccurs rule scannerRules →
  Local.sourceState rule ≡ doneState →
  ⊥
doneStateHasNoResidentRule Local.ruleHere ()
doneStateHasNoResidentRule (Local.ruleThere Local.ruleHere) ()
doneStateHasNoResidentRule (Local.ruleThere (Local.ruleThere ())) sourceEq

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Arbitrarily large unary-framed integers can now be skipped with constant
-- finite control, one transition per true payload bit plus one terminating edge.
-- This is the first literal parser fragment needed by the self-delimiting
-- universal interpreter; value comparison/storage remain separate microcode.
------------------------------------------------------------------------
