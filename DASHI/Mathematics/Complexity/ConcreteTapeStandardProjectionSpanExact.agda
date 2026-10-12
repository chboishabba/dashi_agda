module DASHI.Mathematics.Complexity.ConcreteTapeStandardProjectionSpanExact where

------------------------------------------------------------------------
-- CANONICAL CONCRETE -> STANDARD PROJECTION PRESERVES TAPE SPAN
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (trans)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural

appendLength :
  ∀ {A : Set} (xs ys : List A) →
  Structural.listLength (Local.append xs ys)
  ≡ Structural.listLength xs + Structural.listLength ys
appendLength [] ys = refl
appendLength (x ∷ xs) ys
  rewrite appendLength xs ys = refl

plainCellsToSymbolsLength :
  ∀ {State Symbol : Set}
    {cells : List (Local.TapeCell State Symbol)}
    (plain : WF.PlainCells cells) →
  Structural.listLength (Canonical.plainCellsToSymbols plain)
  ≡ Structural.listLength cells
plainCellsToSymbolsLength WF.plainNil = refl
plainCellsToSymbolsLength (WF.plainCons rest)
  rewrite plainCellsToSymbolsLength rest = refl

appendSymbolFarLeftSpan :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    (symbol : Symbol)
    (configuration : Standard.StandardConfiguration machine) →
  Structural.configurationSpan
    (Canonical.appendSymbolFarLeft symbol configuration)
  ≡ suc (Structural.configurationSpan configuration)
appendSymbolFarLeftSpan symbol configuration
  rewrite appendLength
    (Standard.left configuration)
    (symbol ∷ [])
        | NatP.+-suc
            (Structural.listLength (Standard.left configuration))
            zero
        | NatP.+-identityʳ
            (Structural.listLength (Standard.left configuration)) =
  refl

canonicalProjectionCellsSpanExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    {cells : List
      (Local.TapeCell (Local.State machine) (Local.Symbol machine))}
    (unique : WF.ExactlyOneHead cells) →
  Structural.configurationSpan
    (Canonical.canonicalProjectionCells unique)
  ≡ Structural.listLength cells
canonicalProjectionCellsSpanExact
    (WF.headHere restPlain)
  rewrite plainCellsToSymbolsLength restPlain = refl
canonicalProjectionCellsSpanExact
    (WF.plainBefore {symbol = symbol} unique)
  rewrite appendSymbolFarLeftSpan
            symbol
            (Canonical.canonicalProjectionCells unique)
        | canonicalProjectionCellsSpanExact unique =
  refl

coordinateLengthExact :
  ∀ {A : Set} (xs : List A) →
  Structural.listLength xs ≡ Coordinate.listLength xs
coordinateLengthExact [] = refl
coordinateLengthExact (x ∷ xs)
  rewrite coordinateLengthExact xs = refl

guardedStandardStartSpanExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Structural.configurationSpan
    (Language.guardedStandardStart input steps)
  ≡ Guard.guardedInitialCols input steps
guardedStandardStartSpanExact input steps =
  trans
    (canonicalProjectionCellsSpanExact
      (Language.guardedInitialUnique input steps))
    (trans
      (coordinateLengthExact (Guard.guardedInitialCells input steps))
      (Guard.guardedInitialCellCount input steps))

------------------------------------------------------------------------
-- RESOURCE CONSEQUENCE
--
-- The conventional split-tape configuration used by the candidate execution
-- has exactly the same represented span as the literal guarded concrete row:
--
--   initialInputCellCount(input) + 2*T.
--
-- Combined with structural simulation, no hidden configuration-size expansion
-- is available in the middle phase.
------------------------------------------------------------------------
