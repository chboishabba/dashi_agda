module DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact where

------------------------------------------------------------------------
-- ARBITRARY FIXED-WIDTH SAT BITS -> CONCRETE ROWS AND SHARED RULE
--
-- Cook--Levin soundness starts from an arbitrary satisfying assignment, not
-- necessarily a canonical one-hot encoding of a known run.  The canonical
-- cell codec already has a total decoder, so we use fixed row dimensions to
-- partition arbitrary bits into cell blocks.  No encode-after-decode theorem
-- is required: malformed blocks simply decode to the codec's deterministic
-- fallback values, while every occurrence of the same global block decodes
-- identically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

RowBitsWidth :
  Local.ConcreteTapeMachine → Nat → Nat
RowBitsWidth machine cells =
  cells * Canonical.CellWidth machine

decodeCells :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (count : Nat) →
  CNF.Bits (RowBitsWidth machine count) →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
decodeCells stateCoverage symbolCoverage zero CNF.[]ᵇ =
  []
decodeCells {machine} stateCoverage symbolCoverage
    (suc count) bits =
  Canonical.decodeCell stateCoverage symbolCoverage
      (Canonical.takeBits
        (Canonical.CellWidth machine)
        bits)
  ∷
  decodeCells stateCoverage symbolCoverage count
    (Canonical.dropBits
      (Canonical.CellWidth machine)
      bits)

decodeCellsLength :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (count : Nat)
    (bits : CNF.Bits (RowBitsWidth machine count)) →
  Canonical.listLength
    (decodeCells stateCoverage symbolCoverage count bits)
  ≡ count
decodeCellsLength stateCoverage symbolCoverage zero CNF.[]ᵇ =
  refl
decodeCellsLength stateCoverage symbolCoverage
    (suc count) bits
    rewrite decodeCellsLength
      stateCoverage symbolCoverage count
      (Canonical.dropBits
        (Canonical.CellWidth _)
        bits) =
  refl

decodeRow :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (count : Nat) →
  CNF.Bits (RowBitsWidth machine count) →
  Local.TapeRow machine
decodeRow stateCoverage symbolCoverage count bits =
  Local.tape-row
    (decodeCells
      stateCoverage symbolCoverage count bits)

record FixedTableauShape : Set where
  field
    rowCount : Nat
    columnCount : Nat

open FixedTableauShape public

TableauBitsWidth :
  (machine : Local.ConcreteTapeMachine) →
  FixedTableauShape →
  Nat
TableauBitsWidth machine shape =
  rowCount shape * RowBitsWidth machine (columnCount shape)

decodeRows :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rows cols : Nat) →
  CNF.Bits (rows * RowBitsWidth machine cols) →
  List (Local.TapeRow machine)
decodeRows stateCoverage symbolCoverage zero cols CNF.[]ᵇ =
  []
decodeRows {machine} stateCoverage symbolCoverage
    (suc rows) cols bits =
  decodeRow stateCoverage symbolCoverage cols
      (Canonical.takeBits
        (RowBitsWidth machine cols)
        bits)
  ∷
  decodeRows stateCoverage symbolCoverage rows cols
    (Canonical.dropBits
      (RowBitsWidth machine cols)
      bits)

decodeRowsLength :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rows cols : Nat)
    (bits : CNF.Bits (rows * RowBitsWidth machine cols)) →
  Canonical.listLength
    (decodeRows
      stateCoverage symbolCoverage rows cols bits)
  ≡ rows
decodeRowsLength stateCoverage symbolCoverage
    zero cols CNF.[]ᵇ =
  refl
decodeRowsLength stateCoverage symbolCoverage
    (suc rows) cols bits
    rewrite decodeRowsLength
      stateCoverage symbolCoverage rows cols
      (Canonical.dropBits
        (RowBitsWidth _ cols)
        bits) =
  refl

record FixedTransitionShape
    (machine : Local.ConcreteTapeMachine) : Set where
  field
    columnCount : Nat

open FixedTransitionShape public

TransitionAssignmentWidth :
  (machine : Local.ConcreteTapeMachine) →
  FixedTransitionShape machine →
  Nat
TransitionAssignmentWidth machine shape =
  Selector.RuleWidth machine +
  (RowBitsWidth machine (columnCount shape) +
   RowBitsWidth machine (columnCount shape))

record DecodedTransition
    (machine : Local.ConcreteTapeMachine)
    (shape : FixedTransitionShape machine) : Set₁ where
  field
    rule :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)
    ruleOccurs :
      Local.RuleOccurs rule (Local.rules machine)
    before after : Local.TapeRow machine
    beforeWidth :
      Canonical.listLength (Local.cells before)
      ≡ columnCount shape
    afterWidth :
      Canonical.listLength (Local.cells after)
      ≡ columnCount shape

open DecodedTransition public

decodeTransition :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (shape : FixedTransitionShape machine) →
  CNF.Bits (TransitionAssignmentWidth machine shape) →
  DecodedTransition machine shape
decodeTransition {machine}
    stateCoverage symbolCoverage nonempty shape bits =
  record
    { rule =
        Selector.decodeRule nonempty selectorBits
    ; ruleOccurs =
        Selector.decodeRuleOccurs nonempty selectorBits
    ; before =
        decodeRow stateCoverage symbolCoverage
          (columnCount shape) beforeBits
    ; after =
        decodeRow stateCoverage symbolCoverage
          (columnCount shape) afterBits
    ; beforeWidth =
        decodeCellsLength
          stateCoverage symbolCoverage
          (columnCount shape) beforeBits
    ; afterWidth =
        decodeCellsLength
          stateCoverage symbolCoverage
          (columnCount shape) afterBits
    }
  where
    selectorBits =
      Canonical.takeBits
        (Selector.RuleWidth machine)
        bits

    rowPairBits =
      Canonical.dropBits
        (Selector.RuleWidth machine)
        bits

    beforeBits =
      Canonical.takeBits
        (RowBitsWidth machine (columnCount shape))
        rowPairBits

    afterBits =
      Canonical.dropBits
        (RowBitsWidth machine (columnCount shape))
        rowPairBits

record ArbitraryAssignmentDecodeReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine)
    symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)
    nonemptyRules :
      Selector.NonemptyRuleTable machine

    arbitraryRowBitsDecodePaid : Bool
    decodedRowLengthExactPaid : Bool
    arbitrarySelectorDecodesToMachineRulePaid : Bool
    arbitraryTransitionDecodePaid : Bool
    fixedTableauRowDecodePaid : Bool
    overlapDecodeConsistencyPaid : Bool
    globalTransitionCNFSoundPaid : Bool
    runLevelDecodePaid : Bool
    endpointDecodePaid : Bool
    acceptingAssignmentIffRunPaid : Bool
    polynomialReductionPaid : Bool
    pVsNPResolved : Bool

canonicalArbitraryAssignmentDecodeReceipt :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine) →
  ArbitraryAssignmentDecodeReceipt machine
canonicalArbitraryAssignmentDecodeReceipt
    machine stateCoverage symbolCoverage nonempty = record
  { stateCoverage = stateCoverage
  ; symbolCoverage = symbolCoverage
  ; nonemptyRules = nonempty
  ; arbitraryRowBitsDecodePaid = true
  ; decodedRowLengthExactPaid = true
  ; arbitrarySelectorDecodesToMachineRulePaid = true
  ; arbitraryTransitionDecodePaid = true
  ; fixedTableauRowDecodePaid = true
  ; overlapDecodeConsistencyPaid = false
  ; globalTransitionCNFSoundPaid = false
  ; runLevelDecodePaid = false
  ; endpointDecodePaid = false
  ; acceptingAssignmentIffRunPaid = false
  ; polynomialReductionPaid = false
  ; pVsNPResolved = false
  }
