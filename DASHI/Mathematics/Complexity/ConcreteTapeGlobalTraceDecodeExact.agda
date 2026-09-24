module DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact where

------------------------------------------------------------------------
-- ONE GLOBAL SAT VECTOR -> T+1 ROWS + T SHARED MACHINE-RULE CHOICES
--
-- Layout:
--
--   allRowsBits || allSelectorBits
--
-- with fixed column count C and step count T:
--
--   rows      : (T+1) * (C * CellWidth)
--   selectors : T * RuleWidth
--
-- Arbitrary bits decode totality-first: every row block becomes a concrete
-- TapeRow and every selector block becomes a theorem-bearing RuleOccurs choice.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

RowsTraceWidth :
  Local.ConcreteTapeMachine → Nat → Nat → Nat
RowsTraceWidth machine steps cols =
  suc steps * Decode.RowBitsWidth machine cols

SelectorsTraceWidth :
  Local.ConcreteTapeMachine → Nat → Nat
SelectorsTraceWidth machine steps =
  steps * Selector.RuleWidth machine

GlobalTraceWidth :
  Local.ConcreteTapeMachine → Nat → Nat → Nat
GlobalTraceWidth machine steps cols =
  RowsTraceWidth machine steps cols
  + SelectorsTraceWidth machine steps

decodeSelectors :
  ∀ {machine}
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps : Nat) →
  CNF.Bits (SelectorsTraceWidth machine steps) →
  List (Selector.ListedRule (Local.rules machine))
decodeSelectors nonempty zero CNF.[]ᵇ =
  []
decodeSelectors {machine} nonempty (suc steps) bits =
  Selector.decodeRuleChoice nonempty
      (Canonical.takeBits
        (Selector.RuleWidth machine)
        bits)
  ∷
  decodeSelectors nonempty steps
    (Canonical.dropBits
      (Selector.RuleWidth machine)
      bits)

decodeSelectorsLength :
  ∀ {machine}
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps : Nat)
    (bits : CNF.Bits (SelectorsTraceWidth machine steps)) →
  Canonical.listLength (decodeSelectors nonempty steps bits)
  ≡ steps
decodeSelectorsLength nonempty zero CNF.[]ᵇ =
  refl
decodeSelectorsLength nonempty (suc steps) bits
    rewrite decodeSelectorsLength nonempty steps
      (Canonical.dropBits
        (Selector.RuleWidth _)
        bits) =
  refl


data AllRowsHaveWidth
    {machine : Local.ConcreteTapeMachine}
    (cols : Nat) :
    List (Local.TapeRow machine) → Set where
  allRowsWidthNil :
    AllRowsHaveWidth cols []
  allRowsWidthCons :
    ∀ {row rows} →
    Canonical.listLength (Local.cells row) ≡ cols →
    AllRowsHaveWidth cols rows →
    AllRowsHaveWidth cols (row ∷ rows)

decodeRowsAllHaveWidth :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rows cols : Nat)
    (bits : CNF.Bits (rows * Decode.RowBitsWidth machine cols)) →
  AllRowsHaveWidth cols
    (Decode.decodeRows
      stateCoverage symbolCoverage rows cols bits)
decodeRowsAllHaveWidth stateCoverage symbolCoverage
    zero cols CNF.[]ᵇ =
  allRowsWidthNil
decodeRowsAllHaveWidth {machine}
    stateCoverage symbolCoverage
    (suc rows) cols bits =
  allRowsWidthCons
    (Decode.decodeCellsLength
      stateCoverage symbolCoverage cols
      (Canonical.takeBits
        (Decode.RowBitsWidth machine cols)
        bits))
    (decodeRowsAllHaveWidth
      stateCoverage symbolCoverage rows cols
      (Canonical.dropBits
        (Decode.RowBitsWidth machine cols)
        bits))

record DecodedGlobalTrace
    (machine : Local.ConcreteTapeMachine)
    (steps cols : Nat) : Set₁ where
  field
    rows : List (Local.TapeRow machine)
    selectors :
      List (Selector.ListedRule (Local.rules machine))

    rowsLength :
      Canonical.listLength rows ≡ suc steps
    selectorsLength :
      Canonical.listLength selectors ≡ steps

    allRowsFixedWidth :
      AllRowsHaveWidth cols rows

    everySelectorInsideMachine :
      (choice : Selector.ListedRule (Local.rules machine)) →
      Local.RuleOccurs
        (Selector.selectedRule choice)
        (Local.rules machine)

open DecodedGlobalTrace public

decodeGlobalTrace :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat) →
  CNF.Bits (GlobalTraceWidth machine steps cols) →
  DecodedGlobalTrace machine steps cols
decodeGlobalTrace {machine}
    stateCoverage symbolCoverage nonempty steps cols bits =
  record
    { rows =
        decodedRows
    ; selectors =
        decodedSelectors
    ; rowsLength =
        Decode.decodeRowsLength
          stateCoverage symbolCoverage
          (suc steps) cols rowsBits
    ; selectorsLength =
        decodeSelectorsLength
          nonempty steps selectorBits
    ; allRowsFixedWidth =
        decodeRowsAllHaveWidth
          stateCoverage symbolCoverage
          (suc steps) cols rowsBits
    ; everySelectorInsideMachine =
        Selector.selectedOccurs
    }
  where
    rowsBits =
      Canonical.takeBits
        (RowsTraceWidth machine steps cols)
        bits

    selectorBits =
      Canonical.dropBits
        (RowsTraceWidth machine steps cols)
        bits

    decodedRows =
      Decode.decodeRows
        stateCoverage symbolCoverage
        (suc steps) cols rowsBits

    decodedSelectors =
      decodeSelectors nonempty steps selectorBits

record GlobalTraceDecodeReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine)
    symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)
    nonemptyRules :
      Selector.NonemptyRuleTable machine

    oneGlobalVectorPaid : Bool
    exactTPlusOneRowsPaid : Bool
    exactTSelectorsPaid : Bool
    selectorsAlwaysInsideMachinePaid : Bool
    fixedColumnDecodePaid : Bool
    adjacentTimeSlicePlacementPaid : Bool
    transitionCNFsOverGlobalVectorPaid : Bool
    initialEndpointCNFPaid : Bool
    acceptingEndpointCNFPaid : Bool
    satisfyingAssignmentIffAcceptingRunPaid : Bool
    polynomialReductionPaid : Bool
    pVsNPResolved : Bool

canonicalGlobalTraceDecodeReceipt :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine) →
  GlobalTraceDecodeReceipt machine
canonicalGlobalTraceDecodeReceipt
    machine stateCoverage symbolCoverage nonempty = record
  { stateCoverage = stateCoverage
  ; symbolCoverage = symbolCoverage
  ; nonemptyRules = nonempty
  ; oneGlobalVectorPaid = true
  ; exactTPlusOneRowsPaid = true
  ; exactTSelectorsPaid = true
  ; selectorsAlwaysInsideMachinePaid = true
  ; fixedColumnDecodePaid = true
  ; adjacentTimeSlicePlacementPaid = false
  ; transitionCNFsOverGlobalVectorPaid = false
  ; initialEndpointCNFPaid = false
  ; acceptingEndpointCNFPaid = false
  ; satisfyingAssignmentIffAcceptingRunPaid = false
  ; polynomialReductionPaid = false
  ; pVsNPResolved = false
  }
