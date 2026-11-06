module DASHI.Mathematics.Complexity.ConcreteTapeDecodedWindowSameObjectExact where

------------------------------------------------------------------------
-- RAW SIX-CELL SAT SLICE = WINDOW OF THE ACTUAL DECODED ADJACENT ROWS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
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
    (leftMap : Fin.Fin m → Fin.Fin global)
    (rightMap : Fin.Fin n → Fin.Fin global)
    (bits : CNF.Bits global) →
  Rename.pullbackBits
    (Placement.finSumCases leftMap rightMap) bits
  ≡
  Canonical.appendBits
    (Rename.pullbackBits leftMap bits)
    (Rename.pullbackBits rightMap bits)
pullbackFinSumCases {m = zero} leftMap rightMap bits =
  refl
pullbackFinSumCases {m = suc m} leftMap rightMap bits
    rewrite pullbackFinSumCases
      (λ i → leftMap (Fin.suc i)) rightMap bits =
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
    (Canonical.decodeCell {machine} stateCoverage symbolCoverage
      (Slice.blockSliceBits {width = Canonical.CellWidth machine} slot bits))
    (Decode.decodeCells {machine} stateCoverage symbolCoverage count bits)
decodeCellsAtBlockSlice {machine} stateCoverage symbolCoverage
    Global.here bits =
  Indexed.here
decodeCellsAtBlockSlice {machine}
    stateCoverage symbolCoverage
    (Global.there slot) bits =
  Indexed.there
    (decodeCellsAtBlockSlice {machine}
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
    (Canonical.decodeCell {machine} stateCoverage symbolCoverage
      (Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowLeftSlot start) bits))
    (Canonical.decodeCell {machine} stateCoverage symbolCoverage
      (Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowCenterSlot start) bits))
    (Canonical.decodeCell {machine} stateCoverage symbolCoverage
      (Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowRightSlot start) bits))
    (Local.cells (Decode.decodeRow
      stateCoverage symbolCoverage cols bits))
decodedRowTriple {machine} stateCoverage symbolCoverage start bits =
  record
    { leftAt =
        decodeCellsAtBlockSlice {machine}
          stateCoverage symbolCoverage
          (Raw.windowLeftSlot start) bits
    ; centerAt =
        decodeCellsAtBlockSlice {machine}
          stateCoverage symbolCoverage
          (Raw.windowCenterSlot start) bits
    ; rightAt =
        decodeCellsAtBlockSlice {machine}
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
    (Raw.globalCellRename {machine} {steps} {cols} rowSlot cellSlot)
    globalBits
  ≡
  Slice.blockSliceBits {width = Canonical.CellWidth machine} cellSlot
    (Global.rowSliceBits {machine} {steps} {cols} rowSlot globalBits)
globalCellBits_eq_rowBlockSlice {machine} {steps} {cols} rowSlot cellSlot globalBits =
  trans
    (pullbackCompose
      (Global.blockRename cellSlot)
      (Global.globalRowRename {machine} {steps} {cols} rowSlot)
      globalBits)
    (Slice.pullbackBlockRename_eq_blockSlice
      {width = Canonical.CellWidth machine}
      cellSlot
      (Global.rowSliceBits {machine} {steps} {cols} rowSlot globalBits))

sixCellRawBits :
  ∀ {machine steps cols timeIndex columnIndex}
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  CNF.Bits (Canonical.WindowWidth machine)
sixCellRawBits {machine} {steps} {cols} timeSlot start globalBits =
  Rename.pullbackBits
    (Raw.sixCellGlobalRename {machine} {steps} {cols} timeSlot start) globalBits

sixCellRawBits_decompose :
  ∀ {machine steps cols timeIndex columnIndex}
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  sixCellRawBits {machine} {steps} {cols} timeSlot start globalBits
  ≡
  Canonical.appendBits
    (Rename.pullbackBits
      (Raw.globalCellRename {machine} {steps} {cols}
        (Global.sameSlotInSucc timeSlot)
        (Raw.windowLeftSlot start))
      globalBits)
    (Canonical.appendBits
      (Rename.pullbackBits
        (Raw.globalCellRename {machine} {steps} {cols}
          (Global.sameSlotInSucc timeSlot)
          (Raw.windowCenterSlot start))
        globalBits)
      (Canonical.appendBits
        (Rename.pullbackBits
          (Raw.globalCellRename {machine} {steps} {cols}
            (Global.sameSlotInSucc timeSlot)
            (Raw.windowRightSlot start))
          globalBits)
        (Canonical.appendBits
          (Rename.pullbackBits
            (Raw.globalCellRename {machine} {steps} {cols}
              (Global.nextSlotInSucc timeSlot)
              (Raw.windowLeftSlot start))
            globalBits)
          (Canonical.appendBits
            (Rename.pullbackBits
              (Raw.globalCellRename {machine} {steps} {cols}
                (Global.nextSlotInSucc timeSlot)
                (Raw.windowCenterSlot start))
              globalBits)
            (Rename.pullbackBits
              (Raw.globalCellRename {machine} {steps} {cols}
                (Global.nextSlotInSucc timeSlot)
                (Raw.windowRightSlot start))
              globalBits)))))
sixCellRawBits_decompose {machine} {steps} {cols} timeSlot start globalBits =
  trans step1
    (cong (Canonical.appendBits (Rename.pullbackBits oldLeft globalBits))
      (trans step2
        (cong (Canonical.appendBits (Rename.pullbackBits oldCenter globalBits))
          (trans step3
            (cong (Canonical.appendBits (Rename.pullbackBits oldRight globalBits))
              (trans step4
                (cong (Canonical.appendBits (Rename.pullbackBits newLeft globalBits))
                  step5)))))))
  where
    cw = Canonical.CellWidth machine
    gw = Trace.GlobalTraceWidth machine steps cols

    beforeSlot = Global.sameSlotInSucc timeSlot
    afterSlot = Global.nextSlotInSucc timeSlot

    oldLeft =
      Raw.globalCellRename {machine} {steps} {cols} beforeSlot (Raw.windowLeftSlot start)
    oldCenter =
      Raw.globalCellRename {machine} {steps} {cols} beforeSlot (Raw.windowCenterSlot start)
    oldRight =
      Raw.globalCellRename {machine} {steps} {cols} beforeSlot (Raw.windowRightSlot start)

    newLeft =
      Raw.globalCellRename {machine} {steps} {cols} afterSlot (Raw.windowLeftSlot start)
    newCenter =
      Raw.globalCellRename {machine} {steps} {cols} afterSlot (Raw.windowCenterSlot start)
    newRight =
      Raw.globalCellRename {machine} {steps} {cols} afterSlot (Raw.windowRightSlot start)

    step1 = pullbackFinSumCases {m = cw} {n = cw + (cw + (cw + (cw + cw)))} {global = gw}
      oldLeft
      (Placement.finSumCases {m = cw} {n = cw + (cw + (cw + cw))} {global = gw} oldCenter
        (Placement.finSumCases {m = cw} {n = cw + (cw + cw)} {global = gw} oldRight
          (Placement.finSumCases {m = cw} {n = cw + cw} {global = gw} newLeft
            (Placement.finSumCases {m = cw} {n = cw} {global = gw} newCenter newRight))))
      globalBits

    step2 = pullbackFinSumCases {m = cw} {n = cw + (cw + (cw + cw))} {global = gw}
      oldCenter
      (Placement.finSumCases {m = cw} {n = cw + (cw + cw)} {global = gw} oldRight
        (Placement.finSumCases {m = cw} {n = cw + cw} {global = gw} newLeft
          (Placement.finSumCases {m = cw} {n = cw} {global = gw} newCenter newRight)))
      globalBits

    step3 = pullbackFinSumCases {m = cw} {n = cw + (cw + cw)} {global = gw}
      oldRight
      (Placement.finSumCases {m = cw} {n = cw + cw} {global = gw} newLeft
        (Placement.finSumCases {m = cw} {n = cw} {global = gw} newCenter newRight))
      globalBits

    step4 = pullbackFinSumCases {m = cw} {n = cw + cw} {global = gw}
      newLeft
      (Placement.finSumCases {m = cw} {n = cw} {global = gw} newCenter newRight)
      globalBits

    step5 = pullbackFinSumCases {m = cw} {n = cw} {global = gw}
      newCenter newRight globalBits

rawSelectedRuleBits_eq_selectorSliceBits :
  ∀ {machine steps cols timeIndex columnIndex}
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Canonical.takeBits (Selector.RuleWidth machine)
    (Raw.rawSelectedWindowBits {machine} {steps} {cols} timeSlot start globalBits)
  ≡
  Global.selectorSliceBits {machine} {steps} {cols} timeSlot globalBits
rawSelectedRuleBits_eq_selectorSliceBits {machine} {steps} {cols}
    timeSlot start globalBits =
  trans
    (cong (Canonical.takeBits (Selector.RuleWidth machine))
      (pullbackFinSumCases
        {m = Selector.RuleWidth machine}
        {n = Canonical.WindowWidth machine}
        {global = Trace.GlobalTraceWidth machine steps cols}
        (Global.globalSelectorRename {machine} {steps} {cols} timeSlot)
        (Raw.sixCellGlobalRename {machine} {steps} {cols} timeSlot start)
        globalBits))
    (Canonical.takeAppendBits
      {m = Selector.RuleWidth machine}
      {n = Canonical.WindowWidth machine}
      (Global.selectorSliceBits {machine} {steps} {cols} timeSlot globalBits)
      (sixCellRawBits {machine} {steps} {cols} timeSlot start globalBits))

rawSelectedSixBits_eq_sixCellRawBits :
  ∀ {machine steps cols timeIndex columnIndex}
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Canonical.dropBits (Selector.RuleWidth machine)
    (Raw.rawSelectedWindowBits {machine} {steps} {cols} timeSlot start globalBits)
  ≡ sixCellRawBits {machine} {steps} {cols} timeSlot start globalBits
rawSelectedSixBits_eq_sixCellRawBits {machine} {steps} {cols}
    timeSlot start globalBits =
  trans
    (cong (Canonical.dropBits (Selector.RuleWidth machine))
      (pullbackFinSumCases
        {m = Selector.RuleWidth machine}
        {n = Canonical.WindowWidth machine}
        {global = Trace.GlobalTraceWidth machine steps cols}
        (Global.globalSelectorRename {machine} {steps} {cols} timeSlot)
        (Raw.sixCellGlobalRename {machine} {steps} {cols} timeSlot start)
        globalBits))
    (Canonical.dropAppendBits
      {m = Selector.RuleWidth machine}
      {n = Canonical.WindowWidth machine}
      (Global.selectorSliceBits {machine} {steps} {cols} timeSlot globalBits)
      (sixCellRawBits {machine} {steps} {cols} timeSlot start globalBits))

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

decodedAdjacentWindowFromRows :
  ∀ {machine cols columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (start : Raw.WindowStart columnIndex cols)
    (beforeBits afterBits : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Indexed.IndexedSixCellWindow machine
    (Decode.decodeRow stateCoverage symbolCoverage cols beforeBits)
    (Decode.decodeRow stateCoverage symbolCoverage cols afterBits)
decodedAdjacentWindowFromRows {machine} {cols}
    stateCoverage symbolCoverage start beforeBits afterBits =
  record
    { index = _
    ; oldLeft =
        Canonical.decodeCell {machine} stateCoverage symbolCoverage
          (Slice.blockSliceBits {width = Canonical.CellWidth machine}
            (Raw.windowLeftSlot start) beforeBits)
    ; oldCenter =
        Canonical.decodeCell {machine} stateCoverage symbolCoverage
          (Slice.blockSliceBits {width = Canonical.CellWidth machine}
            (Raw.windowCenterSlot start) beforeBits)
    ; oldRight =
        Canonical.decodeCell {machine} stateCoverage symbolCoverage
          (Slice.blockSliceBits {width = Canonical.CellWidth machine}
            (Raw.windowRightSlot start) beforeBits)
    ; newLeft =
        Canonical.decodeCell {machine} stateCoverage symbolCoverage
          (Slice.blockSliceBits {width = Canonical.CellWidth machine}
            (Raw.windowLeftSlot start) afterBits)
    ; newCenter =
        Canonical.decodeCell {machine} stateCoverage symbolCoverage
          (Slice.blockSliceBits {width = Canonical.CellWidth machine}
            (Raw.windowCenterSlot start) afterBits)
    ; newRight =
        Canonical.decodeCell {machine} stateCoverage symbolCoverage
          (Slice.blockSliceBits {width = Canonical.CellWidth machine}
            (Raw.windowRightSlot start) afterBits)
    ; oldTriple =
        decodedRowTriple {machine}
          stateCoverage symbolCoverage start beforeBits
    ; newTriple =
        decodedRowTriple {machine}
          stateCoverage symbolCoverage start afterBits
    }

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
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.sameSlotInSucc timeSlot) globalBits))
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.nextSlotInSucc timeSlot) globalBits))
decodedAdjacentWindow {machine} {steps} {cols}
    stateCoverage symbolCoverage timeSlot start globalBits =
  decodedAdjacentWindowFromRows stateCoverage symbolCoverage start
    (Global.rowSliceBits {machine} {steps} {cols}
      (Global.sameSlotInSucc timeSlot) globalBits)
    (Global.rowSliceBits {machine} {steps} {cols}
      (Global.nextSlotInSucc timeSlot) globalBits)

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
    (Raw.rawSelectedWindowBits {machine} {steps} {cols} timeSlot start globalBits)
  ≡
  Indexed.forgetIndex
    (decodedAdjacentWindow {machine} {steps} {cols}
      stateCoverage symbolCoverage timeSlot start globalBits)
decodedRawWindowEqualsAdjacentRowsWindow
    {machine} {steps} {cols} stateCoverage symbolCoverage nonempty
    timeSlot start globalBits =
  trans eq1 (trans eq2 (trans eq3 eq4))
  where
    codec =
      Canonical.canonicalWindowCodec
        machine stateCoverage symbolCoverage

    beforeBits =
      Global.rowSliceBits {machine} {steps} {cols}
        (Global.sameSlotInSucc timeSlot) globalBits
    afterBits =
      Global.rowSliceBits {machine} {steps} {cols}
        (Global.nextSlotInSucc timeSlot) globalBits

    b1 = Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowLeftSlot start) beforeBits
    b2 = Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowCenterSlot start) beforeBits
    b3 = Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowRightSlot start) beforeBits
    b4 = Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowLeftSlot start) afterBits
    b5 = Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowCenterSlot start) afterBits
    b6 = Slice.blockSliceBits {width = Canonical.CellWidth machine} (Raw.windowRightSlot start) afterBits

    p1 = globalCellBits_eq_rowBlockSlice {machine} {steps} {cols}
      (Global.sameSlotInSucc timeSlot) (Raw.windowLeftSlot start) globalBits
    p2 = globalCellBits_eq_rowBlockSlice {machine} {steps} {cols}
      (Global.sameSlotInSucc timeSlot) (Raw.windowCenterSlot start) globalBits
    p3 = globalCellBits_eq_rowBlockSlice {machine} {steps} {cols}
      (Global.sameSlotInSucc timeSlot) (Raw.windowRightSlot start) globalBits
    p4 = globalCellBits_eq_rowBlockSlice {machine} {steps} {cols}
      (Global.nextSlotInSucc timeSlot) (Raw.windowLeftSlot start) globalBits
    p5 = globalCellBits_eq_rowBlockSlice {machine} {steps} {cols}
      (Global.nextSlotInSucc timeSlot) (Raw.windowCenterSlot start) globalBits
    p6 = globalCellBits_eq_rowBlockSlice {machine} {steps} {cols}
      (Global.nextSlotInSucc timeSlot) (Raw.windowRightSlot start) globalBits

    bitsEq =
      cong₂ Canonical.appendBits p1
        (cong₂ Canonical.appendBits p2
          (cong₂ Canonical.appendBits p3
            (cong₂ Canonical.appendBits p4
              (cong₂ Canonical.appendBits p5 p6))))

    eq1 =
      cong (Window.decode codec)
        (rawSelectedSixBits_eq_sixCellRawBits {machine} {steps} {cols}
          timeSlot start globalBits)

    eq2 =
      cong (Window.decode codec)
        (sixCellRawBits_decompose {machine} {steps} {cols}
          timeSlot start globalBits)

    eq3 =
      cong (Window.decode codec) bitsEq

    eq4 =
      decodeCanonicalSixAppend {machine = machine}
        stateCoverage symbolCoverage
        b1 b2 b3 b4 b5 b6

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
