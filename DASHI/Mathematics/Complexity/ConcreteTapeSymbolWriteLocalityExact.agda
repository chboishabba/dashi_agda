module DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact where

------------------------------------------------------------------------
-- ERASE HEAD/CONTROL DECORATION: ONE MACHINE STEP WRITES AT MOST ONE SYMBOL
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

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
-- A same-position single-symbol rewrite relation.
------------------------------------------------------------------------

data AtMostOneSymbolWrite {Symbol : Set} :
    List Symbol → List Symbol → Set where
  noWrite :
    ∀ {symbols} →
    AtMostOneSymbolWrite symbols symbols

  writeHere :
    ∀ {prefix old new suffix} →
    AtMostOneSymbolWrite
      (Local.append prefix (old ∷ suffix))
      (Local.append prefix (new ∷ suffix))

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
      writeHere
... | Local.realizes-stay
    with Local.beforeShape (Local.occurrence witness)
       | Local.afterShape (Local.occurrence witness)
...   | refl | refl
      rewrite eraseAppend (Local.prefix (Local.occurrence witness)) _
            | eraseAppend (Local.prefix (Local.occurrence witness)) _ =
      writeHere
... | Local.realizes-right
    with Local.beforeShape (Local.occurrence witness)
       | Local.afterShape (Local.occurrence witness)
...   | refl | refl
      rewrite eraseAppend (Local.prefix (Local.occurrence witness)) _
            | eraseAppend (Local.prefix (Local.occurrence witness)) _ =
      writeHere

------------------------------------------------------------------------
-- Reflexive/transitive bounded-write closure.
------------------------------------------------------------------------

data SymbolWritesWithin {Symbol : Set} :
    Agda.Builtin.Nat.Nat →
    List Symbol → List Symbol → Set where
  writesDone :
    ∀ {symbols} →
    SymbolWritesWithin 0 symbols symbols

  writesStep :
    ∀ {steps start middle finish} →
    AtMostOneSymbolWrite start middle →
    SymbolWritesWithin steps middle finish →
    SymbolWritesWithin (Agda.Builtin.Nat.suc steps) start finish

------------------------------------------------------------------------
-- RESOURCE FIREWALL
--
-- A concrete T-step execution can perform at most T same-position symbol
-- rewrites after head/control decoration is erased.  A downstream quotation
-- generator must therefore pay content creation in this currency; blank padding
-- supplies space but not written information.
------------------------------------------------------------------------
