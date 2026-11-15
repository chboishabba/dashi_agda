module DASHI.Mathematics.Complexity.ConcreteTapeDecodedWholeRowSemanticExact where

------------------------------------------------------------------------
-- ALL RAW SEMANTIC WINDOWS = ALL WINDOWS OF THE ACTUAL DECODED ROW PAIR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst; subst₂)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeArbitrarySelectedWindowSemanticExact as Semantic
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedWindowSameObjectExact as Same
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapePlacedWholeRowCNFExact as IndexedScan
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- The indexed window list selected by raw allWindowStarts
------------------------------------------------------------------------

decodedWindowsForStartsFromRows :
  ∀ {machine cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (starts : List (Transition.SomeWindowStart cols))
    (beforeBits afterBits : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  List
    (Indexed.IndexedSixCellWindow machine
      (Decode.decodeRow stateCoverage symbolCoverage cols beforeBits)
      (Decode.decodeRow stateCoverage symbolCoverage cols afterBits))
decodedWindowsForStartsFromRows stateCoverage symbolCoverage [] beforeBits afterBits = []
decodedWindowsForStartsFromRows {machine} {cols} stateCoverage symbolCoverage
    (Transition.some-window-start index start ∷ rest) beforeBits afterBits =
  Same.decodedAdjacentWindowFromRows stateCoverage symbolCoverage start beforeBits afterBits
  ∷ decodedWindowsForStartsFromRows stateCoverage symbolCoverage rest beforeBits afterBits

decodedWindowsForStarts :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (timeSlot : Global.Slot timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  List
    (Indexed.IndexedSixCellWindow machine
      (Decode.decodeRow stateCoverage symbolCoverage cols
        (Global.rowSliceBits {machine} {steps} {cols}
          (Global.sameSlotInSucc timeSlot) globalBits))
      (Decode.decodeRow stateCoverage symbolCoverage cols
        (Global.rowSliceBits {machine} {steps} {cols}
          (Global.nextSlotInSucc timeSlot) globalBits)))
decodedWindowsForStarts {machine} {steps} {cols} stateCoverage symbolCoverage
    timeSlot starts globalBits =
  decodedWindowsForStartsFromRows stateCoverage symbolCoverage starts
    (Global.rowSliceBits {machine} {steps} {cols}
      (Global.sameSlotInSucc timeSlot) globalBits)
    (Global.rowSliceBits {machine} {steps} {cols}
      (Global.nextSlotInSucc timeSlot) globalBits)

------------------------------------------------------------------------
-- Legality transfers immediately through the P1 same-object equality
------------------------------------------------------------------------

ruleAtTime :
  ∀ {machine steps cols timeIndex}
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Local.TapeRule (Local.State machine) (Local.Symbol machine)
ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits =
  Selector.decodeRule nonempty
    (Global.selectorSliceBits {machine} {steps} {cols} timeSlot globalBits)

semanticRule_eq_ruleAtTime :
  ∀ {machine steps cols timeIndex index}
    {stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine)}
    {symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)}
    {nonempty : Selector.NonemptyRuleTable machine}
    {timeSlot : Global.Slot timeIndex steps}
    {start : Raw.WindowStart index cols}
    {globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)}
    (semantic :
      Semantic.RawDecodedWindowSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot start globalBits) →
  Semantic.rule semantic
  ≡ ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits
semanticRule_eq_ruleAtTime
    {machine} {steps} {cols}
    {nonempty = nonempty}
    {timeSlot = timeSlot}
    {start = start}
    {globalBits = globalBits}
    semantic =
  trans
    (Semantic.ruleExact semantic)
    (cong (Selector.decodeRule nonempty)
      (Same.rawSelectedRuleBits_eq_selectorSliceBits {machine} {steps} {cols}
        timeSlot start globalBits))

rawSemanticToDecodedIndexedLegal :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Scan.AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits starts →
  IndexedScan.AllIndexedLegal {machine}
    (ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits)
    (decodedWindowsForStarts {machine} {steps} {cols}
      stateCoverage symbolCoverage timeSlot starts globalBits)
rawSemanticToDecodedIndexedLegal {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot [] globalBits Scan.semanticWindowsDone =
  IndexedScan.allIndexedNil
rawSemanticToDecodedIndexedLegal {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot
    (Transition.some-window-start index start ∷ rest)
    globalBits
    (Scan.semanticWindowsStep current remaining) =
  IndexedScan.allIndexedCons currentLegal
    (rawSemanticToDecodedIndexedLegal {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty
      timeSlot rest globalBits remaining)
  where
    currentLegal :
      Pattern.LegalWindowForRule machine
        (ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits)
        (Indexed.forgetIndex
          (Same.decodedAdjacentWindow {machine} {steps} {cols}
            stateCoverage symbolCoverage timeSlot start globalBits))
    currentLegal =
      subst₂ (Pattern.LegalWindowForRule machine)
        (semanticRule_eq_ruleAtTime {machine} {steps} {cols} current)
        (trans (Semantic.windowExact current)
          (Same.decodedRawWindowEqualsAdjacentRowsWindow {machine} {steps} {cols}
            stateCoverage symbolCoverage nonempty timeSlot start globalBits))
        (Semantic.legal current)

------------------------------------------------------------------------
-- The only list-level same-object fact required above the local P1 theorem.
--
-- Both lists recurse as:
--   head window at coordinate zero
--   :: shift every window of the one-cell tail.
-- Hence this is structural on cols.
------------------------------------------------------------------------

decodedWindowsForStarts_mapShift :
  ∀ {machine cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (starts : List (Transition.SomeWindowStart cols))
    (beforeBits afterBits : CNF.Bits (Decode.RowBitsWidth machine (suc cols))) →
  decodedWindowsForStartsFromRows stateCoverage symbolCoverage
    (Transition.mapShiftWindowStarts starts) beforeBits afterBits
  ≡
  IndexedScan.mapShiftIndexedWindows
    (Canonical.decodeCell {machine} stateCoverage symbolCoverage
      (Canonical.takeBits (Canonical.CellWidth machine) beforeBits))
    (Canonical.decodeCell {machine} stateCoverage symbolCoverage
      (Canonical.takeBits (Canonical.CellWidth machine) afterBits))
    (decodedWindowsForStartsFromRows stateCoverage symbolCoverage starts
      (Canonical.dropBits (Canonical.CellWidth machine) beforeBits)
      (Canonical.dropBits (Canonical.CellWidth machine) afterBits))
decodedWindowsForStarts_mapShift stateCoverage symbolCoverage [] beforeBits afterBits = refl
decodedWindowsForStarts_mapShift {machine} stateCoverage symbolCoverage
    (Transition.some-window-start index start ∷ rest) beforeBits afterBits =
  cong
    (Same.decodedAdjacentWindowFromRows stateCoverage symbolCoverage (Raw.there start) beforeBits afterBits ∷_)
    (decodedWindowsForStarts_mapShift stateCoverage symbolCoverage rest beforeBits afterBits)

decodedAllStarts_eq_indexedScanFromRows :
  ∀ {machine cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (beforeBits afterBits : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  decodedWindowsForStartsFromRows stateCoverage symbolCoverage
    (Transition.allWindowStarts cols) beforeBits afterBits
  ≡
  IndexedScan.scanIndexedWindows machine
    (Decode.decodeRow stateCoverage symbolCoverage cols beforeBits)
    (Decode.decodeRow stateCoverage symbolCoverage cols afterBits)
decodedAllStarts_eq_indexedScanFromRows {cols = zero} stateCoverage symbolCoverage beforeBits afterBits = refl
decodedAllStarts_eq_indexedScanFromRows {cols = suc zero} stateCoverage symbolCoverage beforeBits afterBits = refl
decodedAllStarts_eq_indexedScanFromRows {cols = suc (suc zero)} stateCoverage symbolCoverage beforeBits afterBits = refl
decodedAllStarts_eq_indexedScanFromRows {machine} {cols = suc (suc (suc rest))}
    stateCoverage symbolCoverage beforeBits afterBits =
  cong (head ∷_)
    (trans
      (decodedWindowsForStarts_mapShift stateCoverage symbolCoverage
        (Transition.allWindowStarts (suc (suc rest))) beforeBits afterBits)
      (cong
        (IndexedScan.mapShiftIndexedWindows
          (Canonical.decodeCell {machine} stateCoverage symbolCoverage
            (Canonical.takeBits (Canonical.CellWidth machine) beforeBits))
          (Canonical.decodeCell {machine} stateCoverage symbolCoverage
            (Canonical.takeBits (Canonical.CellWidth machine) afterBits)))
        (decodedAllStarts_eq_indexedScanFromRows {machine} {cols = suc (suc rest)}
          stateCoverage symbolCoverage
          (Canonical.dropBits (Canonical.CellWidth machine) beforeBits)
          (Canonical.dropBits (Canonical.CellWidth machine) afterBits))))
  where
    head =
      Same.decodedAdjacentWindowFromRows stateCoverage symbolCoverage
        Raw.here beforeBits afterBits

decodedAllStarts_eq_indexedScan :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  decodedWindowsForStarts
    stateCoverage symbolCoverage timeSlot
    (Transition.allWindowStarts cols) globalBits
  ≡
  IndexedScan.scanIndexedWindows machine
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.sameSlotInSucc timeSlot) globalBits))
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.nextSlotInSucc timeSlot) globalBits))
decodedAllStarts_eq_indexedScan {machine} {steps} {cols}
    stateCoverage symbolCoverage timeSlot globalBits =
  decodedAllStarts_eq_indexedScanFromRows {machine} {cols}
    stateCoverage symbolCoverage
    (Global.rowSliceBits {machine} {steps} {cols} (Global.sameSlotInSucc timeSlot) globalBits)
    (Global.rowSliceBits {machine} {steps} {cols} (Global.nextSlotInSucc timeSlot) globalBits)

------------------------------------------------------------------------
-- P2: raw semantic scan -> actual Whole.AllWindowsLegal
------------------------------------------------------------------------

allIndexedLegalToAllWindowsLegal :
  ∀ {machine rule before after}
    (legal :
      IndexedScan.AllIndexedLegal rule
        (IndexedScan.scanIndexedWindows machine before after)) →
  Whole.AllWindowsLegal machine rule before after
allIndexedLegalToAllWindowsLegal {machine} {rule} {before} {after} legal =
  subst
    (Whole.All (Pattern.LegalWindowForRule machine rule))
    (IndexedScan.scanIndexed_forget machine before after)
    (go legal)
  where
    go :
      ∀ {occurrences} →
      IndexedScan.AllIndexedLegal rule occurrences →
      Whole.All
        (Pattern.LegalWindowForRule machine rule)
        (IndexedScan.mapForgetIndexed occurrences)
    go IndexedScan.allIndexedNil =
      Whole.allNil
    go (IndexedScan.allIndexedCons current rest) =
      Whole.allCons current (go rest)

allRawWindowsSemanticToDecodedAllWindowsLegal :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Scan.AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits
    (Transition.allWindowStarts cols) →
  Whole.AllWindowsLegal machine
    (ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits)
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.sameSlotInSucc timeSlot) globalBits))
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.nextSlotInSucc timeSlot) globalBits))
allRawWindowsSemanticToDecodedAllWindowsLegal {machine} {steps}
    {cols = zero}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits Scan.semanticWindowsDone =
  Whole.allNil
allRawWindowsSemanticToDecodedAllWindowsLegal {machine} {steps}
    {cols = suc zero}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits Scan.semanticWindowsDone =
  Whole.allNil
allRawWindowsSemanticToDecodedAllWindowsLegal {machine} {steps}
    {cols = suc (suc zero)}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits Scan.semanticWindowsDone =
  Whole.allNil
allRawWindowsSemanticToDecodedAllWindowsLegal
    {machine} {steps} {cols = suc (suc (suc rest))}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits semantics =
  allIndexedLegalToAllWindowsLegal {machine}
    (subst
      (IndexedScan.AllIndexedLegal {machine}
        (ruleAtTime {machine} {steps} {suc (suc (suc rest))} nonempty timeSlot globalBits))
      (decodedAllStarts_eq_indexedScan {machine} {steps} {suc (suc (suc rest))}
        stateCoverage symbolCoverage timeSlot globalBits)
      (rawSemanticToDecodedIndexedLegal {machine} {steps} {suc (suc (suc rest))}
        stateCoverage symbolCoverage nonempty
        timeSlot (Transition.allWindowStarts (suc (suc (suc rest))))
        globalBits semantics))



------------------------------------------------------------------------
-- Converse: decoded whole-row legality -> raw semantic witnesses
------------------------------------------------------------------------

allWindowsLegalToAllIndexed :
  ∀ {machine rule before after} →
  Whole.AllWindowsLegal machine rule before after →
  IndexedScan.AllIndexedLegal rule
    (IndexedScan.scanIndexedWindows machine before after)
allWindowsLegalToAllIndexed {machine} {rule} {before} {after} legal =
  go (IndexedScan.scanIndexedWindows machine before after)
    (subst
      (Whole.All (Pattern.LegalWindowForRule machine rule))
      (sym (IndexedScan.scanIndexed_forget machine before after))
      legal)
  where
    go :
      ∀ occurrences →
      Whole.All
        (Pattern.LegalWindowForRule machine rule)
        (IndexedScan.mapForgetIndexed occurrences) →
      IndexedScan.AllIndexedLegal rule occurrences
    go [] Whole.allNil =
      IndexedScan.allIndexedNil
    go (window ∷ rest) (Whole.allCons current remaining) =
      IndexedScan.allIndexedCons current (go rest remaining)

headAllIndexedLegal :
  ∀ {machine rule before after w ws} →
  IndexedScan.AllIndexedLegal {machine} rule {before} {after} (w ∷ ws) →
  Pattern.LegalWindowForRule machine rule (Indexed.forgetIndex w)
headAllIndexedLegal (IndexedScan.allIndexedCons legal _) = legal

tailAllIndexedLegal :
  ∀ {machine rule before after w ws} →
  IndexedScan.AllIndexedLegal {machine} rule {before} {after} (w ∷ ws) →
  IndexedScan.AllIndexedLegal {machine} rule {before} {after} ws
tailAllIndexedLegal (IndexedScan.allIndexedCons _ rest) = rest

decodedIndexedLegalToRawSemantic :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  IndexedScan.AllIndexedLegal {machine}
    (ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits)
    (decodedWindowsForStarts {machine} {steps} {cols}
      stateCoverage symbolCoverage timeSlot starts globalBits) →
  Scan.AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits starts
decodedIndexedLegalToRawSemantic {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot [] globalBits legal =
  Scan.semanticWindowsDone
decodedIndexedLegalToRawSemantic {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot
    (Transition.some-window-start index start ∷ rest)
    globalBits
    legal =
  Scan.semanticWindowsStep
    semanticCurrent
    (decodedIndexedLegalToRawSemantic {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty
      timeSlot rest globalBits
      (tailAllIndexedLegal legal))
  where
    semanticCurrent :
      Semantic.RawDecodedWindowSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot start globalBits
    semanticCurrent =
      record
        { rule =
            ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits
        ; window =
            Indexed.forgetIndex
              (Same.decodedAdjacentWindow {machine} {steps} {cols}
                stateCoverage symbolCoverage
                timeSlot start globalBits)
        ; ruleExact =
            sym
              (cong
                (Selector.decodeRule nonempty)
                (Same.rawSelectedRuleBits_eq_selectorSliceBits {machine} {steps} {cols}
                  timeSlot start globalBits))
        ; windowExact =
            sym
              (Same.decodedRawWindowEqualsAdjacentRowsWindow {machine} {steps} {cols}
                stateCoverage symbolCoverage nonempty
                timeSlot start globalBits)
        ; legal = headAllIndexedLegal legal
        }

decodedAllWindowsLegalToRawSemantic :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Whole.AllWindowsLegal machine
    (ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits)
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.sameSlotInSucc timeSlot) globalBits))
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.nextSlotInSucc timeSlot) globalBits)) →
  Scan.AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits
    (Transition.allWindowStarts cols)
decodedAllWindowsLegalToRawSemantic {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits legal =
  decodedIndexedLegalToRawSemantic {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot (Transition.allWindowStarts cols)
    globalBits
    (subst
      (IndexedScan.AllIndexedLegal {machine}
        (ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits))
      (sym
        (decodedAllStarts_eq_indexedScan {machine} {steps} {cols}
          stateCoverage symbolCoverage timeSlot globalBits))
      (allWindowsLegalToAllIndexed {machine} legal))

record DecodedWholeRowSemanticReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    rawStartsToIndexedDecodedWindowsPaid : Bool
    decodedStartsEqualNativeIndexedScanPaid : Bool
    rawLegalityTransfersToIndexedScanPaid : Bool
    indexedScanForgetsToWholeScanPaid : Bool
    rawSemanticToDecodedAllWindowsLegalPaid : Bool

decodedWholeRowSemanticReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  DecodedWholeRowSemanticReceipt machine
decodedWholeRowSemanticReceipt machine = record
  { rawStartsToIndexedDecodedWindowsPaid = true
  ; decodedStartsEqualNativeIndexedScanPaid = true
  ; rawLegalityTransfersToIndexedScanPaid = true
  ; indexedScanForgetsToWholeScanPaid = true
  ; rawSemanticToDecodedAllWindowsLegalPaid = true
  }
