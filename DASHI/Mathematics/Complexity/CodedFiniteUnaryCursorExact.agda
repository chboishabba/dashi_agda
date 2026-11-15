module DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact where

------------------------------------------------------------------------
-- LITERAL UNARY-INDEX CURSOR AS A CODED FINITE STANDARD TM
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase

blankSymbol : Fin.Fin 3
blankSymbol = Fin.zero

moreSymbol : Fin.Fin 3
moreSymbol = Fin.suc Fin.zero

stopSymbol : Fin.Fin 3
stopSymbol = Fin.suc (Fin.suc Fin.zero)

moreNotStop : moreSymbol ≡ stopSymbol → ⊥
moreNotStop ()

cursorRule : Local.TapeRule (Fin.Fin 1) (Fin.Fin 3)
cursorRule =
  Local.tape-rule
    Fin.zero
    moreSymbol
    Fin.zero
    moreSymbol
    Local.moveRight

cursorSourceDispatchUnique :
  ∀ {left right : Local.TapeRule (Fin.Fin 1) (Fin.Fin 3)} →
  Local.RuleOccurs left (cursorRule ∷ []) →
  Local.RuleOccurs right (cursorRule ∷ []) →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right
cursorSourceDispatchUnique Local.ruleHere Local.ruleHere sourceEq readEq = refl
cursorSourceDispatchUnique Local.ruleHere (Local.ruleThere ()) sourceEq readEq
cursorSourceDispatchUnique (Local.ruleThere ()) second sourceEq readEq

cursorSourceCode : Coded.CodedFiniteStandardTM
cursorSourceCode = record
  { Coded.stateCount = 1
  ; Coded.symbolCount = 3
  ; Coded.blank = blankSymbol
  ; Coded.initialState = Fin.zero
  ; Coded.acceptingState = Fin.zero
  ; Coded.rules = cursorRule ∷ []
  ; Coded.dispatchUnique = cursorSourceDispatchUnique
  }

cursorCode : Nat → Coded.CodedFiniteStandardTM
cursorCode n = Phase.phaseLiftCode cursorSourceCode n

cursorFragment : (n : Nat) → Mode.CodedModeFragment 3
cursorFragment n = Phase.phaseLiftFragment cursorSourceCode n

cursorState :
  (n : Nat) →
  Fin.Fin (suc n) →
  Fin.Fin (Coded.stateCount cursorSourceCode * suc n)
cursorState n phase = Phase.phaseState Fin.zero phase

cursorInitialStateExact :
  (n : Nat) →
  Coded.initialState (cursorCode n) ≡ cursorState n Fin.zero
cursorInitialStateExact n = refl

cursorTerminalStateExact :
  (n : Nat) →
  Coded.acceptingState (cursorCode n)
    ≡ cursorState n (Phase.lastPhase n)
cursorTerminalStateExact n = refl

cursorResidentReadsMore :
  (n : Nat) →
  ∀ {resident} →
  Local.RuleOccurs resident (Mode.rules (cursorFragment n)) →
  Local.readSymbol resident ≡ moreSymbol
cursorResidentReadsMore n residentOccurs
  with Phase.phaseTablePreimage (Coded.allFin n) residentOccurs
... | phase , original , originalOccurs , exact
  with originalOccurs
... | Local.ruleHere rewrite exact = refl
... | Local.ruleThere ()

cursorStopKeyFresh :
  (n : Nat) →
  (phase : Fin.Fin (suc n)) →
  ∀ {resident}
    (residentOccurs : Local.RuleOccurs resident (Coded.rules (cursorCode n))) →
  Local.sourceState resident ≡ cursorState n phase →
  Local.readSymbol resident ≡ stopSymbol →
  ⊥
cursorStopKeyFresh n phase residentOccurs sourceEq readEq =
  moreNotStop
    (transRead residentOccurs readEq)
  where
    transRead :
      ∀ {resident} →
      Local.RuleOccurs resident (Coded.rules (cursorCode n)) →
      Local.readSymbol resident ≡ stopSymbol →
      moreSymbol ≡ stopSymbol
    transRead occurs equality
      rewrite cursorResidentReadsMore n occurs = equality

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The unary counter is literal finite standard-TM syntax. It consumes one
-- `more` per edge, and every `stop` dispatch key is disjoint from all resident
-- cursor rules, at every phase including overflow.
------------------------------------------------------------------------
