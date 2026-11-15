module DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact where

------------------------------------------------------------------------
-- ERASE HEAD/CONTROL DECORATION: ONE MACHINE STEP WRITES AT MOST ONE SYMBOL
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run

cellSymbol :
  ∀ {State Symbol : Set} →
  Local.TapeCell State Symbol → Symbol
cellSymbol (Local.plain symbol) = symbol
cellSymbol (Local.headed state symbol) = symbol

eraseCells :
  ∀ {State Symbol : Set} →
  List (Local.TapeCell State Symbol) →
  List Symbol
eraseCells [] = []
eraseCells (cell ∷ cells) =
  cellSymbol cell ∷ eraseCells cells

eraseRow :
  ∀ {machine : Local.ConcreteTapeMachine} →
  Local.TapeRow machine →
  List (Local.Symbol machine)
eraseRow row = eraseCells (Local.cells row)

eraseAppend :
  ∀ {State Symbol : Set}
    (left right : List (Local.TapeCell State Symbol)) →
  eraseCells (Local.append left right)
  ≡ Local.append (eraseCells left) (eraseCells right)
eraseAppend [] right = refl
eraseAppend (cell ∷ left) right
  rewrite eraseAppend left right = refl

------------------------------------------------------------------------
-- A same-position at-most-one-symbol rewrite relation.
------------------------------------------------------------------------

data AtMostOneSymbolWrite {Symbol : Set} :
    List Symbol → List Symbol → Set where
  noWrite :
    ∀ {symbols} →
    AtMostOneSymbolWrite symbols symbols

  writeHead :
    ∀ {old new rest} →
    AtMostOneSymbolWrite
      (old ∷ rest)
      (new ∷ rest)

  keepHead :
    ∀ {symbol before after} →
    AtMostOneSymbolWrite before after →
    AtMostOneSymbolWrite
      (symbol ∷ before)
      (symbol ∷ after)

prependSame :
  ∀ {Symbol : Set}
    (prefix : List Symbol)
    {before after : List Symbol} →
  AtMostOneSymbolWrite before after →
  AtMostOneSymbolWrite
    (Local.append prefix before)
    (Local.append prefix after)
prependSame [] rewrite = rewrite
prependSame (symbol ∷ prefix) rewrite =
  keepHead (prependSame prefix rewrite)

centerWrite :
  ∀ {Symbol : Set}
    {left old new right : Symbol}
    {suffix : List Symbol} →
  AtMostOneSymbolWrite
    (left ∷ old ∷ right ∷ suffix)
    (left ∷ new ∷ right ∷ suffix)
centerWrite = keepHead writeHead

------------------------------------------------------------------------
-- Every directional local machine rule erases to exactly that relation.
------------------------------------------------------------------------

machineStepErasesToAtMostOneWrite :
  ∀ {machine before after} →
  Local.MachineStep machine before after →
  AtMostOneSymbolWrite (eraseRow before) (eraseRow after)
machineStepErasesToAtMostOneWrite witness
    with Local.ruleIsConfigured witness
... | Local.realizes-left
    with Local.beforeShape (Local.occurrence witness)
       | Local.afterShape (Local.occurrence witness)
...   | refl | refl
      rewrite eraseAppend (Local.prefix (Local.occurrence witness)) _
            | eraseAppend (Local.prefix (Local.occurrence witness)) _ =
      prependSame
        (eraseCells (Local.prefix (Local.occurrence witness)))
        centerWrite
... | Local.realizes-stay
    with Local.beforeShape (Local.occurrence witness)
       | Local.afterShape (Local.occurrence witness)
...   | refl | refl
      rewrite eraseAppend (Local.prefix (Local.occurrence witness)) _
            | eraseAppend (Local.prefix (Local.occurrence witness)) _ =
      prependSame
        (eraseCells (Local.prefix (Local.occurrence witness)))
        centerWrite
... | Local.realizes-right
    with Local.beforeShape (Local.occurrence witness)
       | Local.afterShape (Local.occurrence witness)
...   | refl | refl
      rewrite eraseAppend (Local.prefix (Local.occurrence witness)) _
            | eraseAppend (Local.prefix (Local.occurrence witness)) _ =
      prependSame
        (eraseCells (Local.prefix (Local.occurrence witness)))
        centerWrite

wellFormedStepErasesToAtMostOneWrite :
  ∀ {machine before after} →
  WF.WellFormedMachineStep machine before after →
  AtMostOneSymbolWrite (eraseRow before) (eraseRow after)
wellFormedStepErasesToAtMostOneWrite step =
  machineStepErasesToAtMostOneWrite (WF.step step)

------------------------------------------------------------------------
-- Reflexive/transitive bounded-write closure.
------------------------------------------------------------------------

data SymbolWritesWithin {Symbol : Set} :
    Nat → List Symbol → List Symbol → Set where
  writesDone :
    ∀ {symbols} →
    SymbolWritesWithin zero symbols symbols

  writesStep :
    ∀ {steps start middle finish} →
    AtMostOneSymbolWrite start middle →
    SymbolWritesWithin steps middle finish →
    SymbolWritesWithin (suc steps) start finish

wellFormedRunErasesToWritesWithin :
  ∀ {machine start rows finish}
    (run : Run.WellFormedTapeRun machine start rows finish) →
  SymbolWritesWithin
    (Run.runLength run)
    (eraseRow start)
    (eraseRow finish)
wellFormedRunErasesToWritesWithin Run.runDone =
  writesDone
wellFormedRunErasesToWritesWithin (Run.runStep step rest) =
  writesStep
    (wellFormedStepErasesToAtMostOneWrite step)
    (wellFormedRunErasesToWritesWithin rest)

------------------------------------------------------------------------
-- RESOURCE FIREWALL
--
-- A concrete T-step execution performs at most T same-position symbol rewrites
-- after head/control decoration is erased. Blank padding supplies address space;
-- it does not supply the quotation's symbol content for free.
------------------------------------------------------------------------
