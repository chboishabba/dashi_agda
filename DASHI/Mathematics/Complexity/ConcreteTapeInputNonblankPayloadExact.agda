module DASHI.Mathematics.Complexity.ConcreteTapeInputNonblankPayloadExact where

------------------------------------------------------------------------
-- INITIAL INPUT ROW NONBLANK CONTENT = INPUT PAYLOAD NONBLANK CONTENT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact as Writes
import DASHI.Mathematics.Complexity.ConcreteTapeNonblankWriteBoundExact as Nonblank
import DASHI.Mathematics.Complexity.ConcreteTapeGuardedNonblankExact as GuardedNonblank

plainSymbolsEraseExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (symbols : List (Local.Symbol machine)) →
  Writes.eraseCells (Input.plainSymbols {machine} symbols)
  ≡ symbols
plainSymbolsEraseExact [] = refl
plainSymbolsEraseExact (symbol ∷ symbols)
  rewrite plainSymbolsEraseExact symbols = refl

appendPlainBlankEraseExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (symbols : List (Local.Symbol machine)) →
  Writes.eraseCells (Input.appendPlainBlank {machine} symbols)
  ≡ Local.append symbols (Local.blank machine ∷ [])
appendPlainBlankEraseExact {machine} symbols
  rewrite Writes.eraseAppend
            (Input.plainSymbols symbols)
            (Local.plain (Local.blank machine) ∷ [])
        | plainSymbolsEraseExact symbols =
  refl

appendBlankNonblankExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (symbols : List (Local.Symbol machine)) →
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    (Local.append symbols (Local.blank machine ∷ []))
  ≡
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    symbols
appendBlankNonblankExact {machine} symbols
  rewrite GuardedNonblank.nonblankCountAppend
            (Local.finiteSymbol machine)
            (Local.blank machine)
            symbols
            (Local.blank machine ∷ [])
        | Nonblank.blankBitZero
            (Local.finiteSymbol machine)
            (Local.blank machine)
        | NatP.+-identityʳ
            (Nonblank.nonblankCount
              (Local.finiteSymbol machine)
              (Local.blank machine)
              symbols) =
  refl

initialInputNonblankExactPayload :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    (Writes.eraseCells (Input.initialInputCells input))
  ≡
  Nonblank.nonblankCount
    (Local.finiteSymbol machine)
    (Local.blank machine)
    input
initialInputNonblankExactPayload {machine} []
  rewrite Nonblank.blankBitZero
            (Local.finiteSymbol machine)
            (Local.blank machine) =
  refl
initialInputNonblankExactPayload {machine} (symbol ∷ [])
  rewrite Nonblank.blankBitZero
            (Local.finiteSymbol machine)
            (Local.blank machine) =
  refl
initialInputNonblankExactPayload {machine} (symbol ∷ next ∷ rest)
  rewrite Nonblank.blankBitZero
            (Local.finiteSymbol machine)
            (Local.blank machine)
        | appendPlainBlankEraseExact {machine} rest
        | appendBlankNonblankExact {machine} rest =
  refl

guardedInputNonblankExactPayload :
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
    input
guardedInputNonblankExactPayload input steps =
  trans
    (GuardedNonblank.guardedRowNonblankExactInitial input steps)
    (initialInputNonblankExactPayload input)

------------------------------------------------------------------------
-- Boundary blanks and T-step guard padding carry no payload information.
------------------------------------------------------------------------
