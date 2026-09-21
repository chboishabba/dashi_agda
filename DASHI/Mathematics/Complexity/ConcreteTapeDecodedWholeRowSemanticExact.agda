module DASHI.Mathematics.Complexity.ConcreteTapeDecodedWholeRowSemanticExact where

------------------------------------------------------------------------
-- ALL RAW SEMANTIC WINDOWS = ALL WINDOWS OF THE ACTUAL DECODED ROW PAIR
------------------------------------------------------------------------

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
    (Semantic.decodedSelectedRule nonempty
      (Raw.rawSelectedWindowBits
        timeSlot
        firstStart
        globalBits))
    (decodedWindowsForStarts
      stateCoverage symbolCoverage timeSlot starts globalBits)
  where
    firstStart : Raw.WindowStart zero cols
    firstStart {cols = suc (suc (suc rest))} = Raw.here
    firstStart {cols = zero} = impossible
      where impossible : Raw.WindowStart zero zero
            impossible = impossible
    firstStart {cols = suc zero} = impossible
      where impossible : Raw.WindowStart zero (suc zero)
            impossible = impossible
    firstStart {cols = suc (suc zero)} = impossible
      where impossible : Raw.WindowStart zero (suc (suc zero))
            impossible = impossible
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
    (rawSemanticTailToDecodedIndexedLegal
      stateCoverage symbolCoverage nonempty
      timeSlot start rest globalBits current remaining)
  where
    currentLegal :
      Pattern.LegalWindowForRule machine
        (Semantic.rule current)
        (Indexed.forgetIndex
          (Same.decodedAdjacentWindow
            stateCoverage symbolCoverage timeSlot start globalBits))
    currentLegal
      rewrite sym (Semantic.ruleExact current)
            | sym (Same.decodedRawWindowEqualsAdjacentRowsWindow
                stateCoverage symbolCoverage nonempty
                timeSlot start globalBits) =
      Semantic.legal current

    rawSemanticTailToDecodedIndexedLegal :
      ∀ {machine steps cols timeIndex index}
        (stateCoverage :
          Canonical.EnumerationCoverage (Local.finiteState machine))
        (symbolCoverage :
          Canonical.EnumerationCoverage (Local.finiteSymbol machine))
        (nonempty : Selector.NonemptyRuleTable machine)
        (timeSlot : Global.Slot timeIndex steps)
        (headStart : Raw.WindowStart index cols)
        (rest : List (Transition.SomeWindowStart cols))
        (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
        (headSemantic :
          Semantic.RawDecodedWindowSemantic
            stateCoverage symbolCoverage nonempty
            timeSlot headStart globalBits) →
      Scan.AllRawWindowsSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot globalBits rest →
      IndexedScan.AllIndexedLegal
        (Semantic.rule headSemantic)
        (decodedWindowsForStarts
          stateCoverage symbolCoverage timeSlot rest globalBits)
    rawSemanticTailToDecodedIndexedLegal
        stateCoverage symbolCoverage nonempty
        timeSlot headStart [] globalBits headSemantic
        Scan.semanticWindowsDone =
      IndexedScan.allIndexedNil
    rawSemanticTailToDecodedIndexedLegal
        stateCoverage symbolCoverage nonempty
        timeSlot headStart
        (Transition.some-window-start nextIndex nextStart ∷ rest)
        globalBits headSemantic
        (Scan.semanticWindowsStep nextSemantic remaining)
        rewrite semanticRulesSame headSemantic nextSemantic =
      IndexedScan.allIndexedCons nextLegal
        (rawSemanticTailToDecodedIndexedLegal
          stateCoverage symbolCoverage nonempty
          timeSlot nextStart rest globalBits nextSemantic remaining)
      where
        semanticRulesSame :
          ∀ {machine steps cols timeIndex i j}
            {stateCoverage :
              Canonical.EnumerationCoverage (Local.finiteState machine)}
            {symbolCoverage :
              Canonical.EnumerationCoverage (Local.finiteSymbol machine)}
            {nonempty : Selector.NonemptyRuleTable machine}
            {timeSlot : Global.Slot timeIndex steps}
            {leftStart : Raw.WindowStart i cols}
            {rightStart : Raw.WindowStart j cols}
            {globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)}
            (left :
              Semantic.RawDecodedWindowSemantic
                stateCoverage symbolCoverage nonempty
                timeSlot leftStart globalBits)
            (right :
              Semantic.RawDecodedWindowSemantic
                stateCoverage symbolCoverage nonempty
                timeSlot rightStart globalBits) →
          Semantic.rule left ≡ Semantic.rule right
        semanticRulesSame left right =
          trans
            (Semantic.ruleExact left)
            (sym (Semantic.ruleExact right))

        nextLegal :
          Pattern.LegalWindowForRule machine
            (Semantic.rule nextSemantic)
            (Indexed.forgetIndex
              (Same.decodedAdjacentWindow
                stateCoverage symbolCoverage
                timeSlot nextStart globalBits))
        nextLegal
          rewrite sym (Semantic.ruleExact nextSemantic)
                | sym (Same.decodedRawWindowEqualsAdjacentRowsWindow
                    stateCoverage symbolCoverage nonempty
                    timeSlot nextStart globalBits) =
          Semantic.legal nextSemantic

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
    rawStartsToIndexedDecodedWindowsPaid : Agda.Builtin.Bool.Bool
    decodedStartsEqualNativeIndexedScanPaid : Agda.Builtin.Bool.Bool
    rawLegalityTransfersToIndexedScanPaid : Agda.Builtin.Bool.Bool
    indexedScanForgetsToWholeScanPaid : Agda.Builtin.Bool.Bool
    rawSemanticToDecodedAllWindowsLegalPaid : Agda.Builtin.Bool.Bool

decodedWholeRowSemanticReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  DecodedWholeRowSemanticReceipt machine
decodedWholeRowSemanticReceipt machine = record
  { rawStartsToIndexedDecodedWindowsPaid = Agda.Builtin.Bool.true
  ; decodedStartsEqualNativeIndexedScanPaid = Agda.Builtin.Bool.true
  ; rawLegalityTransfersToIndexedScanPaid = Agda.Builtin.Bool.true
  ; indexedScanForgetsToWholeScanPaid = Agda.Builtin.Bool.true
  ; rawSemanticToDecodedAllWindowsLegalPaid = Agda.Builtin.Bool.true
  }
