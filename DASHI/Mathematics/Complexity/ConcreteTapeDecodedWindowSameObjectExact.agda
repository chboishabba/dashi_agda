module DASHI.Mathematics.Complexity.ConcreteTapeDecodedWindowSameObjectExact where

------------------------------------------------------------------------
-- RAW SIX-CELL SAT SLICE = WINDOW OF THE ACTUAL DECODED ADJACENT ROWS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.ConcreteTapeArbitrarySelectedWindowSemanticExact as Semantic
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Window
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Generic pullback algebra
------------------------------------------------------------------------

pullbackCompose :
  ∀ {small middle large}
    (first : Fin.Fin small → Fin.Fin middle)
    (second : Fin.Fin middle → Fin.Fin large)
    (bits : CNF.Bits large) →
  Rename.pullbackBits (λ i → second (first i)) bits
  ≡
  Rename.pullbackBits first (Rename.pullbackBits second bits)
pullbackCompose first second bits =
  Placement.bitsExt λ i →
    trans
      (Rename.pullbackLookup (λ j → second (first j)) bits i)
      (trans
        (sym
          (Rename.pullbackLookup second bits (first i)))
        (sym
          (Rename.pullbackLookup first
            (Rename.pullbackBits second bits) i)))

pullbackFinSumCases :
  ∀ {m n global}
    (left : Fin.Fin m → Fin.Fin global)
    (right : Fin.Fin n → Fin.Fin global)
    (bits : CNF.Bits global) →
  Rename.pullbackBits
    (Placement.finSumCases left right) bits
  ≡
  Canonical.appendBits
    (Rename.pullbackBits left bits)
    (Rename.pullbackBits right bits)
pullbackFinSumCases {m = zero} left right bits =
  refl
pullbackFinSumCases {m = suc m} left right bits
    rewrite pullbackFinSumCases
      (λ i → left (Fin.suc i)) right bits =
  refl

------------------------------------------------------------------------
-- A decoded cell really occurs at its fixed-width block coordinate
------------------------------------------------------------------------

decodeCellsAtBlockSlice :
  ∀ {machine index count}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (slot : Global.Slot index count)
    (bits : CNF.Bits (Decode.RowBitsWidth machine count)) →
  Indexed.At index
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Slice.blockSliceBits slot bits))
    (Decode.decodeCells stateCoverage symbolCoverage count bits)
decodeCellsAtBlockSlice stateCoverage symbolCoverage
    Global.here bits =
  Indexed.here
decodeCellsAtBlockSlice {machine}
    stateCoverage symbolCoverage
    (Global.there slot) bits =
  Indexed.there
    (decodeCellsAtBlockSlice
      stateCoverage symbolCoverage slot
      (Canonical.dropBits
        (Canonical.CellWidth machine) bits))

decodedRowTriple :
  ∀ {machine index cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (start : Raw.WindowStart index cols)
    (bits : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Indexed.TripleAt index
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Slice.blockSliceBits (Raw.windowLeftSlot start) bits))
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Slice.blockSliceBits (Raw.windowCenterSlot start) bits))
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Slice.blockSliceBits (Raw.windowRightSlot start) bits))
    (Local.cells (Decode.decodeRow
      stateCoverage symbolCoverage cols bits))
decodedRowTriple stateCoverage symbolCoverage start bits =
  record
    { Indexed.leftAt =
        decodeCellsAtBlockSlice
          stateCoverage symbolCoverage
          (Raw.windowLeftSlot start) bits
    ; Indexed.centerAt =
        decodeCellsAtBlockSlice
          stateCoverage symbolCoverage
          (Raw.windowCenterSlot start) bits
    ; Indexed.rightAt =
        decodeCellsAtBlockSlice
          stateCoverage symbolCoverage
          (Raw.windowRightSlot start) bits
    }

------------------------------------------------------------------------
-- Each raw global cell block is exactly the matching block of rowSliceBits
------------------------------------------------------------------------

globalCellBits_eq_rowBlockSlice :
  ∀ {machine steps cols timeIndex cellIndex}
    (rowSlot : Global.Slot timeIndex (suc steps))
    (cellSlot : Global.Slot cellIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Rename.pullbackBits
    (Raw.globalCellRename rowSlot cellSlot)
    globalBits
  ≡
  Slice.blockSliceBits cellSlot
    (Global.rowSliceBits rowSlot globalBits)
globalCellBits_eq_rowBlockSlice rowSlot cellSlot globalBits =
  trans
    (pullbackCompose
      (Global.blockRename cellSlot)
      (Global.globalRowRename rowSlot)
      globalBits)
    (Slice.pullbackBlockRename_eq_blockSlice
      cellSlot
      (Global.rowSliceBits rowSlot globalBits))

sixCellRawBits :
  ∀ {machine steps cols timeIndex columnIndex}
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  CNF.Bits (Canonical.WindowWidth machine)
sixCellRawBits timeSlot start globalBits =
  Rename.pullbackBits
    (Raw.sixCellGlobalRename timeSlot start) globalBits

sixCellRawBits_decompose :
  ∀ {machine steps cols timeIndex columnIndex}
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  sixCellRawBits timeSlot start globalBits
  ≡
  Canonical.appendBits
    (Rename.pullbackBits
      (Raw.globalCellRename
        (Global.sameSlotInSucc timeSlot)
        (Raw.windowLeftSlot start))
      globalBits)
    (Canonical.appendBits
      (Rename.pullbackBits
        (Raw.globalCellRename
          (Global.sameSlotInSucc timeSlot)
          (Raw.windowCenterSlot start))
        globalBits)
      (Canonical.appendBits
        (Rename.pullbackBits
          (Raw.globalCellRename
            (Global.sameSlotInSucc timeSlot)
            (Raw.windowRightSlot start))
          globalBits)
        (Canonical.appendBits
          (Rename.pullbackBits
            (Raw.globalCellRename
              (Global.nextSlotInSucc timeSlot)
              (Raw.windowLeftSlot start))
            globalBits)
          (Canonical.appendBits
            (Rename.pullbackBits
              (Raw.globalCellRename
                (Global.nextSlotInSucc timeSlot)
                (Raw.windowCenterSlot start))
              globalBits)
            (Rename.pullbackBits
              (Raw.globalCellRename
                (Global.nextSlotInSucc timeSlot)
                (Raw.windowRightSlot start))
              globalBits)))))
sixCellRawBits_decompose timeSlot start globalBits
  rewrite pullbackFinSumCases
    (Raw.globalCellRename
      (Global.sameSlotInSucc timeSlot)
      (Raw.windowLeftSlot start))
    (Placement.finSumCases
      (Raw.globalCellRename
        (Global.sameSlotInSucc timeSlot)
        (Raw.windowCenterSlot start))
      (Placement.finSumCases
        (Raw.globalCellRename
          (Global.sameSlotInSucc timeSlot)
          (Raw.windowRightSlot start))
        (Placement.finSumCases
          (Raw.globalCellRename
            (Global.nextSlotInSucc timeSlot)
            (Raw.windowLeftSlot start))
          (Placement.finSumCases
            (Raw.globalCellRename
              (Global.nextSlotInSucc timeSlot)
              (Raw.windowCenterSlot start))
            (Raw.globalCellRename
              (Global.nextSlotInSucc timeSlot)
              (Raw.windowRightSlot start))))))
    globalBits
  = refl

rawSelectedRuleBits_eq_selectorSliceBits :
  ∀ {machine steps cols timeIndex columnIndex}
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Canonical.takeBits (Selector.RuleWidth machine)
    (Raw.rawSelectedWindowBits timeSlot start globalBits)
  ≡
  Global.selectorSliceBits timeSlot globalBits
rawSelectedRuleBits_eq_selectorSliceBits
    timeSlot start globalBits
  rewrite pullbackFinSumCases
    (Global.globalSelectorRename timeSlot)
    (Raw.sixCellGlobalRename timeSlot start)
    globalBits
        | Canonical.takeAppendBits
            (Global.selectorSliceBits timeSlot globalBits)
            (sixCellRawBits timeSlot start globalBits)
  = refl


rawSelectedSixBits_eq_sixCellRawBits :
  ∀ {machine steps cols timeIndex columnIndex}
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Canonical.dropBits (Selector.RuleWidth machine)
    (Raw.rawSelectedWindowBits timeSlot start globalBits)
  ≡ sixCellRawBits timeSlot start globalBits
rawSelectedSixBits_eq_sixCellRawBits timeSlot start globalBits
  rewrite pullbackFinSumCases
    (Global.globalSelectorRename timeSlot)
    (Raw.sixCellGlobalRename timeSlot start)
    globalBits
        | Canonical.dropAppendBits
            (Rename.pullbackBits
              (Global.globalSelectorRename timeSlot) globalBits)
            (sixCellRawBits timeSlot start globalBits)
  = refl

------------------------------------------------------------------------
-- Canonical six-cell decoding is componentwise canonical cell decoding
------------------------------------------------------------------------

decodeCanonicalSixAppend :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (a b c d e f : CNF.Bits (Canonical.CellWidth machine)) →
  Window.decode
    (Canonical.canonicalWindowCodec
      machine stateCoverage symbolCoverage)
    (Canonical.appendBits a
      (Canonical.appendBits b
        (Canonical.appendBits c
          (Canonical.appendBits d
            (Canonical.appendBits e f)))))
  ≡
  Local.six-cell-window
    (Canonical.decodeCell stateCoverage symbolCoverage a)
    (Canonical.decodeCell stateCoverage symbolCoverage b)
    (Canonical.decodeCell stateCoverage symbolCoverage c)
    (Canonical.decodeCell stateCoverage symbolCoverage d)
    (Canonical.decodeCell stateCoverage symbolCoverage e)
    (Canonical.decodeCell stateCoverage symbolCoverage f)
decodeCanonicalSixAppend
    stateCoverage symbolCoverage a b c d e f
  rewrite Canonical.takeAppendBits a
            (Canonical.appendBits b
              (Canonical.appendBits c
                (Canonical.appendBits d
                  (Canonical.appendBits e f))))
        | Canonical.dropAppendBits a
            (Canonical.appendBits b
              (Canonical.appendBits c
                (Canonical.appendBits d
                  (Canonical.appendBits e f))))
        | Canonical.takeAppendBits b
            (Canonical.appendBits c
              (Canonical.appendBits d
                (Canonical.appendBits e f)))
        | Canonical.dropAppendBits b
            (Canonical.appendBits c
              (Canonical.appendBits d
                (Canonical.appendBits e f)))
        | Canonical.takeAppendBits c
            (Canonical.appendBits d
              (Canonical.appendBits e f))
        | Canonical.dropAppendBits c
            (Canonical.appendBits d
              (Canonical.appendBits e f))
        | Canonical.takeAppendBits d
            (Canonical.appendBits e f)
        | Canonical.dropAppendBits d
            (Canonical.appendBits e f)
        | Canonical.takeAppendBits e f
        | Canonical.dropAppendBits e f
  = refl

------------------------------------------------------------------------
-- The exact adjacent decoded-row window
------------------------------------------------------------------------

decodedAdjacentWindow :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Indexed.IndexedSixCellWindow machine
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits
        (Global.sameSlotInSucc timeSlot) globalBits))
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits
        (Global.nextSlotInSucc timeSlot) globalBits))
decodedAdjacentWindow
    stateCoverage symbolCoverage timeSlot start globalBits =
  record
    { Indexed.index = _
    ; Indexed.oldLeft =
        Canonical.decodeCell stateCoverage symbolCoverage
          (Slice.blockSliceBits
            (Raw.windowLeftSlot start) beforeBits)
    ; Indexed.oldCenter =
        Canonical.decodeCell stateCoverage symbolCoverage
          (Slice.blockSliceBits
            (Raw.windowCenterSlot start) beforeBits)
    ; Indexed.oldRight =
        Canonical.decodeCell stateCoverage symbolCoverage
          (Slice.blockSliceBits
            (Raw.windowRightSlot start) beforeBits)
    ; Indexed.newLeft =
        Canonical.decodeCell stateCoverage symbolCoverage
          (Slice.blockSliceBits
            (Raw.windowLeftSlot start) afterBits)
    ; Indexed.newCenter =
        Canonical.decodeCell stateCoverage symbolCoverage
          (Slice.blockSliceBits
            (Raw.windowCenterSlot start) afterBits)
    ; Indexed.newRight =
        Canonical.decodeCell stateCoverage symbolCoverage
          (Slice.blockSliceBits
            (Raw.windowRightSlot start) afterBits)
    ; Indexed.oldTriple =
        decodedRowTriple
          stateCoverage symbolCoverage start beforeBits
    ; Indexed.newTriple =
        decodedRowTriple
          stateCoverage symbolCoverage start afterBits
    }
  where
    beforeBits =
      Global.rowSliceBits
        (Global.sameSlotInSucc timeSlot) globalBits
    afterBits =
      Global.rowSliceBits
        (Global.nextSlotInSucc timeSlot) globalBits

decodedRawWindowEqualsAdjacentRowsWindow :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Semantic.decodedSelectedWindow stateCoverage symbolCoverage
    (Raw.rawSelectedWindowBits timeSlot start globalBits)
  ≡
  Indexed.forgetIndex
    (decodedAdjacentWindow
      stateCoverage symbolCoverage timeSlot start globalBits)
decodedRawWindowEqualsAdjacentRowsWindow
    {machine} stateCoverage symbolCoverage nonempty
    timeSlot start globalBits
  rewrite rawSelectedSixBits_eq_sixCellRawBits
    timeSlot start globalBits
        | sixCellRawBits_decompose
            timeSlot start globalBits
        | globalCellBits_eq_rowBlockSlice
            (Global.sameSlotInSucc timeSlot)
            (Raw.windowLeftSlot start) globalBits
        | globalCellBits_eq_rowBlockSlice
            (Global.sameSlotInSucc timeSlot)
            (Raw.windowCenterSlot start) globalBits
        | globalCellBits_eq_rowBlockSlice
            (Global.sameSlotInSucc timeSlot)
            (Raw.windowRightSlot start) globalBits
        | globalCellBits_eq_rowBlockSlice
            (Global.nextSlotInSucc timeSlot)
            (Raw.windowLeftSlot start) globalBits
        | globalCellBits_eq_rowBlockSlice
            (Global.nextSlotInSucc timeSlot)
            (Raw.windowCenterSlot start) globalBits
        | globalCellBits_eq_rowBlockSlice
            (Global.nextSlotInSucc timeSlot)
            (Raw.windowRightSlot start) globalBits
        | decodeCanonicalSixAppend
            stateCoverage symbolCoverage
            (Slice.blockSliceBits
              (Raw.windowLeftSlot start) beforeBits)
            (Slice.blockSliceBits
              (Raw.windowCenterSlot start) beforeBits)
            (Slice.blockSliceBits
              (Raw.windowRightSlot start) beforeBits)
            (Slice.blockSliceBits
              (Raw.windowLeftSlot start) afterBits)
            (Slice.blockSliceBits
              (Raw.windowCenterSlot start) afterBits)
            (Slice.blockSliceBits
              (Raw.windowRightSlot start) afterBits)
  = refl
  where
    beforeBits =
      Global.rowSliceBits
        (Global.sameSlotInSucc timeSlot) globalBits
    afterBits =
      Global.rowSliceBits
        (Global.nextSlotInSucc timeSlot) globalBits

record DecodedWindowSameObjectReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    repeatedBlockCellOccurrencePaid : Bool
    rawCellPullbackEqualsDecodedRowBlockPaid : Bool
    rawSixCellDecompositionPaid : Bool
    canonicalWindowComponentDecodePaid : Bool
    rawWindowEqualsAdjacentDecodedRowsWindowPaid : Bool

decodedWindowSameObjectReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  DecodedWindowSameObjectReceipt machine
decodedWindowSameObjectReceipt machine = record
  { repeatedBlockCellOccurrencePaid = true
  ; rawCellPullbackEqualsDecodedRowBlockPaid = true
  ; rawSixCellDecompositionPaid = true
  ; canonicalWindowComponentDecodePaid = true
  ; rawWindowEqualsAdjacentDecodedRowsWindowPaid = true
  }
