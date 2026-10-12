module DASHI.Mathematics.Complexity.ConcreteTapeGuardedNonblankExact where

------------------------------------------------------------------------
-- GUARDED BLANK PADDING ADDS SPACE BUT ZERO NONBLANK CONTENT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeInputPaddingExact as Padding
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact as Writes
import DASHI.Mathematics.Complexity.ConcreteTapeNonblankWriteBoundExact as Nonblank

nonblankBitOneFromDistinct :
  ∀ {Symbol : Set}
    (enumeration : Local.FiniteEnumeration Symbol)
    (blank symbol : Symbol) →
  (symbol ≡ blank → ⊥) →
  Nonblank.nonblankBit enumeration blank symbol ≡ suc zero
nonblankBitOneFromDistinct enumeration blank symbol distinct
    with Local.decideEqual enumeration symbol blank
... | false = refl
... | true =
  ⊥-elim (distinct (Local.decideEqualSound enumeration refl))

nonblankCountAppend :
  ∀ {Symbol : Set}
    (enumeration : Local.FiniteEnumeration Symbol)
    (blank : Symbol)
    (left right : List Symbol) →
  Nonblank.nonblankCount enumeration blank (Local.append left right)
  ≡
  Nonblank.nonblankCount enumeration blank left
    + Nonblank.nonblankCount enumeration blank right
nonblankCountAppend enumeration blank [] right = refl
nonblankCountAppend enumeration blank (symbol ∷ left) right
  rewrite nonblankCountAppend enumeration blank left right
        | NatP.+-assoc
            (Nonblank.nonblankBit enumeration blank symbol)
            (Nonblank.nonblankCount enumeration blank left)
            (Nonblank.nonblankCount enumeration blank right) =
  refl

eraseCellsLength :
  ∀ {State Symbol : Set}
    (cells : List (Local.TapeCell State Symbol)) →
  Nonblank.listLength (Writes.eraseCells cells)
  ≡ Canonical.listLength cells
eraseCellsLength [] = refl
eraseCellsLength (cell ∷ cells)
  rewrite eraseCellsLength cells = refl

replicateBlankNonblankZero :
  ∀ {machine : Local.ConcreteTapeMachine}
    (steps : Nat) →
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    (Writes.eraseCells (Padding.replicateBlank {machine} steps))
  ≡ zero
replicateBlankNonblankZero {machine} zero = refl
replicateBlankNonblankZero {machine} (suc steps)
  rewrite Nonblank.blankBitZero
            (Local.finiteSymbol machine)
            (Local.blank machine)
        | replicateBlankNonblankZero {machine} steps = refl

initialRowNonblankBelowInitialWidth :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    (Writes.eraseCells (Input.initialInputCells input))
  ≤ Input.initialInputCellCount input
initialRowNonblankBelowInitialWidth {machine} input =
  NatP.≤-trans
    (Nonblank.nonblankCountBelowLength
      (Local.finiteSymbol machine)
      (Local.blank machine)
      (Writes.eraseCells (Input.initialInputCells input)))
    lengthExact
  where
    lengthExact :
      Nonblank.listLength (Writes.eraseCells (Input.initialInputCells input))
      ≤ Input.initialInputCellCount input
    lengthExact
      rewrite eraseCellsLength (Input.initialInputCells input) =
      NatP.≤-refl _

guardedRowNonblankExactInitial :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    (Writes.eraseRow (Guard.guardedInitialRow input steps))
  ≡
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    (Writes.eraseCells (Input.initialInputCells input))
guardedRowNonblankExactInitial {machine} input steps
  rewrite Writes.eraseAppend
            (Padding.replicateBlank steps)
            (Local.append
              (Input.initialInputCells input)
              (Padding.replicateBlank steps))
        | Writes.eraseAppend
            (Input.initialInputCells input)
            (Padding.replicateBlank steps)
        | nonblankCountAppend
            (Local.finiteSymbol machine)
            (Local.blank machine)
            (Writes.eraseCells (Padding.replicateBlank steps))
            (Local.append
              (Writes.eraseCells (Input.initialInputCells input))
              (Writes.eraseCells (Padding.replicateBlank steps)))
        | nonblankCountAppend
            (Local.finiteSymbol machine)
            (Local.blank machine)
            (Writes.eraseCells (Input.initialInputCells input))
            (Writes.eraseCells (Padding.replicateBlank steps))
        | replicateBlankNonblankZero {machine} steps
        | NatP.+-identityʳ
            (Nonblank.nonblankCount
              (Local.finiteSymbol machine)
              (Local.blank machine)
              (Writes.eraseCells (Input.initialInputCells input))) =
  refl

guardedRowNonblankBelowInitialWidth :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    (Writes.eraseRow (Guard.guardedInitialRow input steps))
  ≤ Input.initialInputCellCount input
guardedRowNonblankBelowInitialWidth input steps
  rewrite guardedRowNonblankExactInitial input steps =
  initialRowNonblankBelowInitialWidth input

------------------------------------------------------------------------
-- The T blank cells on each side therefore provide address space but no initial
-- nonblank information budget.
------------------------------------------------------------------------
