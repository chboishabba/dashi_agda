module DASHI.Mathematics.Complexity.ConcreteTapeCanonicalProjectionFlattenExact where

------------------------------------------------------------------------
-- FLATTEN(CANONICAL PROJECTION(row)) = ERASED CONCRETE ROW SYMBOLS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.StandardConfigurationFlattenExact as Flatten
import DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact as Writes

plainCellsToSymbolsEraseExact :
  ∀ {State Symbol : Set}
    {cells : List (Local.TapeCell State Symbol)}
    (plain : WF.PlainCells cells) →
  Canonical.plainCellsToSymbols plain
  ≡ Writes.eraseCells cells
plainCellsToSymbolsEraseExact WF.plainNil = refl
plainCellsToSymbolsEraseExact (WF.plainCons rest)
  rewrite plainCellsToSymbolsEraseExact rest = refl

canonicalProjectionCellsFlattenExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    {cells : List
      (Local.TapeCell (Local.State machine) (Local.Symbol machine))}
    (unique : WF.ExactlyOneHead cells) →
  Flatten.flattenConfiguration
    (Canonical.canonicalProjectionCells unique)
  ≡ Writes.eraseCells cells
canonicalProjectionCellsFlattenExact
    (WF.headHere restPlain)
  rewrite plainCellsToSymbolsEraseExact restPlain = refl
canonicalProjectionCellsFlattenExact
    (WF.plainBefore {symbol = symbol} unique)
  rewrite Flatten.flattenAppendSymbolFarLeft
            symbol
            (Canonical.canonicalProjectionCells unique)
        | canonicalProjectionCellsFlattenExact unique =
  refl

canonicalProjectionFlattenExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    {row : Local.TapeRow machine}
    (unique : WF.ExactlyOneHead (Local.cells row)) →
  Flatten.flattenConfiguration
    (Canonical.canonicalProjection unique)
  ≡ Writes.eraseRow row
canonicalProjectionFlattenExact =
  canonicalProjectionCellsFlattenExact

------------------------------------------------------------------------
-- This is the exact content counterpart of projection-span preservation: the
-- standard split-tape view neither invents nor discards underlying tape symbols.
------------------------------------------------------------------------
