module DASHI.Mathematics.Complexity.ConcreteTapeDecodedWholeRowSemanticExact where

------------------------------------------------------------------------
-- ALL RAW SEMANTIC WINDOWS = ALL WINDOWS OF THE ACTUAL DECODED ROW PAIR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

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
        (Global.rowSliceBits
          (Global.sameSlotInSucc timeSlot) globalBits))
      (Decode.decodeRow stateCoverage symbolCoverage cols
        (Global.rowSliceBits
          (Global.nextSlotInSucc timeSlot) globalBits)))
decodedWindowsForStarts stateCoverage symbolCoverage
    timeSlot [] globalBits =
  []
decodedWindowsForStarts stateCoverage symbolCoverage
    timeSlot
    (Transition.some-window-start index start ∷ rest)
    globalBits =
  Same.decodedAdjacentWindow
    stateCoverage symbolCoverage timeSlot start globalBits
  ∷
  decodedWindowsForStarts
    stateCoverage symbolCoverage timeSlot rest globalBits

------------------------------------------------------------------------
-- Legality transfers immediately through the P1 same-object equality
------------------------------------------------------------------------

ruleAtTime :
  ∀ {machine steps cols timeIndex}
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Local.TapeRule (Local.State machine) (Local.Symbol machine)
ruleAtTime nonempty timeSlot globalBits =
  Selector.decodeRule nonempty
    (Global.selectorSliceBits timeSlot globalBits)

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
  ≡ ruleAtTime nonempty timeSlot globalBits
semanticRule_eq_ruleAtTime
    {nonempty = nonempty}
    {timeSlot = timeSlot}
    {start = start}
    {globalBits = globalBits}
    semantic =
  trans
    (Semantic.ruleExact semantic)
    (cong (Selector.decodeRule nonempty)
      (Same.rawSelectedRuleBits_eq_selectorSliceBits
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
  IndexedScan.AllIndexedLegal
    (ruleAtTime nonempty timeSlot globalBits)
    (decodedWindowsForStarts
      stateCoverage symbolCoverage timeSlot starts globalBits)
rawSemanticToDecodedIndexedLegal
    stateCoverage symbolCoverage nonempty
    timeSlot [] globalBits Scan.semanticWindowsDone =
  IndexedScan.allIndexedNil
rawSemanticToDecodedIndexedLegal
    stateCoverage symbolCoverage nonempty
    timeSlot
    (Transition.some-window-start index start ∷ rest)
    globalBits
    (Scan.semanticWindowsStep current remaining) =
  IndexedScan.allIndexedCons currentLegal
    (rawSemanticToDecodedIndexedLegal
      stateCoverage symbolCoverage nonempty
      timeSlot rest globalBits remaining)
  where
    currentLegal :
      Pattern.LegalWindowForRule machine
        (ruleAtTime nonempty timeSlot globalBits)
        (Indexed.forgetIndex
          (Same.decodedAdjacentWindow
            stateCoverage symbolCoverage timeSlot start globalBits))
    currentLegal
      rewrite sym (semanticRule_eq_ruleAtTime current)
            | sym (Same.decodedRawWindowEqualsAdjacentRowsWindow
                stateCoverage symbolCoverage nonempty
                timeSlot start globalBits) =
      Semantic.legal current

------------------------------------------------------------------------
-- The only list-level same-object fact required above the local P1 theorem.
--
-- Both lists recurse as:
--   head window at coordinate zero
--   :: shift every window of the one-cell tail.
-- Hence this is structural on cols.
------------------------------------------------------------------------

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
      (Global.rowSliceBits
        (Global.sameSlotInSucc timeSlot) globalBits))
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits
        (Global.nextSlotInSucc timeSlot) globalBits))
decodedAllStarts_eq_indexedScan
    {cols = zero} stateCoverage symbolCoverage
    timeSlot globalBits =
  refl
decodedAllStarts_eq_indexedScan
    {cols = suc zero} stateCoverage symbolCoverage
    timeSlot globalBits =
  refl
decodedAllStarts_eq_indexedScan
    {cols = suc (suc zero)} stateCoverage symbolCoverage
    timeSlot globalBits =
  refl
decodedAllStarts_eq_indexedScan
    {machine} {steps} {cols = suc (suc (suc rest))}
    stateCoverage symbolCoverage timeSlot globalBits =
  decodedAllStartsSucc
  where
    -- This equality is definitionally driven by the two recursive scanners.
    decodedAllStartsSucc :
      decodedWindowsForStarts
        stateCoverage symbolCoverage timeSlot
        (Transition.allWindowStarts (suc (suc (suc rest))))
        globalBits
      ≡
      IndexedScan.scanIndexedWindows machine
        (Decode.decodeRow stateCoverage symbolCoverage
          (suc (suc (suc rest)))
          (Global.rowSliceBits
            (Global.sameSlotInSucc timeSlot) globalBits))
        (Decode.decodeRow stateCoverage symbolCoverage
          (suc (suc (suc rest)))
          (Global.rowSliceBits
            (Global.nextSlotInSucc timeSlot) globalBits))
    decodedAllStartsSucc = refl

------------------------------------------------------------------------
-- P2: raw semantic scan -> actual Whole.AllWindowsLegal
------------------------------------------------------------------------

allIndexedLegalToAllWindowsLegal :
  ∀ {machine rule before after}
    (legal :
      IndexedScan.AllIndexedLegal rule
        (IndexedScan.scanIndexedWindows machine before after)) →
  Whole.AllWindowsLegal machine rule before after
allIndexedLegalToAllWindowsLegal {machine} {rule} {before} {after} legal
    with IndexedScan.scanIndexed_forget machine before after
... | refl =
  go legal
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
  ΣRuleResult stateCoverage symbolCoverage nonempty
    timeSlot globalBits
  where
    ΣRuleResult :
      ∀ {machine steps cols timeIndex}
        (stateCoverage :
          Canonical.EnumerationCoverage (Local.finiteState machine))
        (symbolCoverage :
          Canonical.EnumerationCoverage (Local.finiteSymbol machine))
        (nonempty : Selector.NonemptyRuleTable machine)
        (timeSlot : Global.Slot timeIndex steps)
        (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
      Set
    ΣRuleResult {machine} {cols = zero}
      stateCoverage symbolCoverage nonempty timeSlot globalBits =
      Whole.AllWindowsLegal machine
        (Selector.decodeRule nonempty
          (Global.selectorSliceBits timeSlot globalBits))
        (Decode.decodeRow stateCoverage symbolCoverage zero
          (Global.rowSliceBits
            (Global.sameSlotInSucc timeSlot) globalBits))
        (Decode.decodeRow stateCoverage symbolCoverage zero
          (Global.rowSliceBits
            (Global.nextSlotInSucc timeSlot) globalBits))
    ΣRuleResult {machine} {cols = suc cols}
      stateCoverage symbolCoverage nonempty timeSlot globalBits =
      Whole.AllWindowsLegal machine
        (Selector.decodeRule nonempty
          (Global.selectorSliceBits timeSlot globalBits))
        (Decode.decodeRow stateCoverage symbolCoverage (suc cols)
          (Global.rowSliceBits
            (Global.sameSlotInSucc timeSlot) globalBits))
        (Decode.decodeRow stateCoverage symbolCoverage (suc cols)
          (Global.rowSliceBits
            (Global.nextSlotInSucc timeSlot) globalBits))
allRawWindowsSemanticToDecodedAllWindowsLegal
    {cols = zero}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits Scan.semanticWindowsDone =
  Whole.allNil
allRawWindowsSemanticToDecodedAllWindowsLegal
    {cols = suc zero}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits Scan.semanticWindowsDone =
  Whole.allNil
allRawWindowsSemanticToDecodedAllWindowsLegal
    {cols = suc (suc zero)}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits Scan.semanticWindowsDone =
  Whole.allNil
allRawWindowsSemanticToDecodedAllWindowsLegal
    {machine} {steps} {cols = suc (suc (suc rest))}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits semantics =
  allIndexedLegalToAllWindowsLegal transported
  where
    rawLegal =
      rawSemanticToDecodedIndexedLegal
        stateCoverage symbolCoverage nonempty
        timeSlot (Transition.allWindowStarts _)
        globalBits semantics

    selectorExact :
      Semantic.decodedSelectedRule nonempty
        (Raw.rawSelectedWindowBits
          timeSlot Raw.here globalBits)
      ≡
      Selector.decodeRule nonempty
        (Global.selectorSliceBits timeSlot globalBits)
    selectorExact =
      cong (Selector.decodeRule nonempty)
        selectorBitsExact
      where
        selectorBitsExact :
          Canonical.takeBits (Selector.RuleWidth machine)
            (Raw.rawSelectedWindowBits
              timeSlot Raw.here globalBits)
          ≡ Global.selectorSliceBits timeSlot globalBits
        selectorBitsExact = refl

    scanExact =
      decodedAllStarts_eq_indexedScan
        stateCoverage symbolCoverage timeSlot globalBits

    transported :
      IndexedScan.AllIndexedLegal
        (Selector.decodeRule nonempty
          (Global.selectorSliceBits timeSlot globalBits))
        (IndexedScan.scanIndexedWindows machine
          (Decode.decodeRow stateCoverage symbolCoverage _
            (Global.rowSliceBits
              (Global.sameSlotInSucc timeSlot) globalBits))
          (Decode.decodeRow stateCoverage symbolCoverage _
            (Global.rowSliceBits
              (Global.nextSlotInSucc timeSlot) globalBits))
    transported
      rewrite sym selectorExact
            | sym scanExact =
      rawLegal

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
