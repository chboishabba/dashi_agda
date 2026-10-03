module DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact where

------------------------------------------------------------------------
-- CANONICAL PROJECTION OF AN EXACTLY-ONE-HEAD CONCRETE ROW
--
-- The earlier one-step weld projected an `InteriorHeadConfiguration` to a
-- conventional split-tape configuration.  That is adequate for one edge but
-- awkward to iterate because the same intermediate row can be accompanied by
-- different interior witnesses.
--
-- This owner removes that proof dependence.  `ExactlyOneHead` already
-- contains exactly the data needed to read a row uniquely.  We recurse through
-- its plain prefix and construct one canonical standard configuration.  The
-- left list is nearest-head-first; therefore a farther-left symbol is appended
-- at the far end of the recursively obtained left list.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

plainCellsToSymbols :
  ∀ {State Symbol : Set}
    {cells : List (Local.TapeCell State Symbol)} →
  WF.PlainCells cells →
  List Symbol
plainCellsToSymbols WF.plainNil = []
plainCellsToSymbols (WF.plainCons {symbol = symbol} rest) =
  symbol ∷ plainCellsToSymbols rest

appendSymbolFarLeft :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol} →
  Symbol →
  Standard.StandardConfiguration machine →
  Standard.StandardConfiguration machine
appendSymbolFarLeft symbol
    (Standard.standard-configuration left q a right) =
  Standard.standard-configuration
    (Local.append left (symbol ∷ [])) q a right

canonicalProjectionCells :
  ∀ {machine : Local.ConcreteTapeMachine}
    {cells : List
      (Local.TapeCell (Local.State machine) (Local.Symbol machine))} →
  WF.ExactlyOneHead cells →
  Standard.StandardConfiguration (Standard.standardControlOfConcrete machine)
canonicalProjectionCells
    (WF.headHere {state = q} {symbol = a} restPlain) =
  Standard.standard-configuration
    [] q a (plainCellsToSymbols restPlain)
canonicalProjectionCells
    (WF.plainBefore {symbol = symbol} unique) =
  appendSymbolFarLeft symbol (canonicalProjectionCells unique)

canonicalProjection :
  ∀ {machine : Local.ConcreteTapeMachine}
    {row : Local.TapeRow machine} →
  WF.ExactlyOneHead (Local.cells row) →
  Standard.StandardConfiguration (Standard.standardControlOfConcrete machine)
canonicalProjection = canonicalProjectionCells

------------------------------------------------------------------------
-- Structural lemmas: projection of a literal plain prefix + headed cell.
------------------------------------------------------------------------

projectPlainPrefix :
  ∀ {machine : Local.ConcreteTapeMachine}
    {prefix rest}
    (prefixPlain : WF.PlainCells prefix)
    (unique : WF.ExactlyOneHead rest) →
  canonicalProjectionCells (WF.prependPlain prefixPlain unique)
    ≡ foldPlainPrefixFarLeft prefixPlain (canonicalProjectionCells unique)
  where
    foldPlainPrefixFarLeft :
      ∀ {State Symbol : Set}
        {cells : List (Local.TapeCell State Symbol)}
        {std : Standard.StandardSingleTapeMachine State Symbol} →
      WF.PlainCells cells →
      Standard.StandardConfiguration std →
      Standard.StandardConfiguration std
    foldPlainPrefixFarLeft WF.plainNil config = config
    foldPlainPrefixFarLeft (WF.plainCons {symbol = symbol} rest) config =
      appendSymbolFarLeft symbol (foldPlainPrefixFarLeft rest config)
projectPlainPrefix WF.plainNil unique = refl
projectPlainPrefix (WF.plainCons prefixPlain) unique
  rewrite projectPlainPrefix prefixPlain unique = refl

------------------------------------------------------------------------
-- A row equality transports canonical projection without changing the value.
------------------------------------------------------------------------

canonicalProjection_transport :
  ∀ {machine : Local.ConcreteTapeMachine}
    {left right : Local.TapeRow machine}
    (eq : Local.cells left ≡ Local.cells right)
    (uniqueLeft : WF.ExactlyOneHead (Local.cells left))
    (uniqueRight : WF.ExactlyOneHead (Local.cells right)) →
  canonicalProjection uniqueLeft ≡ canonicalProjection uniqueRight
canonicalProjection_transport refl uniqueLeft uniqueRight =
  canonicalProjection_uniqueProof uniqueLeft uniqueRight
  where
    canonicalProjection_uniqueProof :
      ∀ {machine : Local.ConcreteTapeMachine}
        {cells : List
          (Local.TapeCell (Local.State machine) (Local.Symbol machine))}
        (u v : WF.ExactlyOneHead cells) →
      canonicalProjectionCells u ≡ canonicalProjectionCells v
    canonicalProjection_uniqueProof
        (WF.headHere p) (WF.headHere q) =
      cong (Standard.standard-configuration [] _ _)
        (plainSymbols_uniqueProof p q)
      where
        plainSymbols_uniqueProof :
          ∀ {State Symbol : Set}
            {cells : List (Local.TapeCell State Symbol)}
            (p q : WF.PlainCells cells) →
          plainCellsToSymbols p ≡ plainCellsToSymbols q
        plainSymbols_uniqueProof WF.plainNil WF.plainNil = refl
        plainSymbols_uniqueProof
            (WF.plainCons p) (WF.plainCons q)
          rewrite plainSymbols_uniqueProof p q = refl
    canonicalProjection_uniqueProof
        (WF.plainBefore u) (WF.plainBefore v)
      rewrite canonicalProjection_uniqueProof u v = refl

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID HERE (subject to exact-head Agda certification):
-- * a canonical split-tape configuration for every ExactlyOneHead row;
-- * no dependence on an arbitrary interior/window decomposition;
-- * proof-irrelevance at the observable projection level;
-- * transport across literal row equality.
--
-- NEXT:
-- * show a deterministic WellFormedMachineStep maps canonical before to
--   canonical after by `Standard.standardNext`;
-- * induct over WellFormedTapeRun, obtaining exact T-step transport;
-- * preserve accepting state and clocks, then freeze machine infrastructure.
------------------------------------------------------------------------
