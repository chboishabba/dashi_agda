module DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact where

------------------------------------------------------------------------
-- LITERAL UNARY-INDEX CURSOR AS A CODED FINITE STANDARD TM
--
-- Symbols:
--   0 = blank
--   1 = more
--   2 = stop
--
-- The source machine has one control state and one resident rule:
--
--   q --more/more,R--> q.
--
-- Its exact n-phase lift therefore gives n+1 cursor states. Reading each
-- `more` advances exactly one phase. Phase n is quiescent by the generic phase
-- compiler. Stop/output links are added separately.
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

cursorStopKeyFresh :
  (n : Nat) →
  (phase : Fin.Fin (suc n)) →
  ∀ {resident}
    (residentOccurs : Local.RuleOccurs resident (Coded.rules (cursorCode n))) →
  Local.sourceState resident ≡ cursorState n phase →
  Local.readSymbol resident ≡ stopSymbol →
  ⊥
cursorStopKeyFresh n phase residentOccurs sourceEq readEq
  with Phase.phaseTablePreimage (Coded.allFin n) residentOccurs
... | residentPhase , original , originalOccurs , exact
  rewrite exact = moreNotStop readEq

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The runtime unary counter is literal finite standard-TM syntax. It consumes
-- one `more` symbol per standard edge and has a fresh `stop` key at every phase.
------------------------------------------------------------------------
