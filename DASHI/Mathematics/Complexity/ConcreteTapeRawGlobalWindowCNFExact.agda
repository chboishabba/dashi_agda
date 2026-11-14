module DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact where

------------------------------------------------------------------------
-- FIXED (time,column) COORDINATE -> LOCAL TRANSITION CNF ON RAW GLOBAL BITS
--
-- This is the reduction-facing version of the window compiler.  It does not
-- start from a known run or an IndexedSixCellWindow witness.  Instead a fixed
-- time slot and a fixed three-column window position determine six cell blocks
-- and one shared rule-selector block directly in the one global SAT vector.
--
-- Pullback layout:
--
--   selector_t
--   || before[t,j] before[t,j+1] before[t,j+2]
--   || after [t+1,j] after [t+1,j+1] after [t+1,j+2]
--
-- The existing total decoders turn arbitrary bits into a concrete rule/window,
-- so truth-table CNF compilation applies to every SAT assignment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Three-consecutive-column witness
------------------------------------------------------------------------

data WindowStart : Nat → Nat → Set where
  here :
    ∀ {rest} →
    WindowStart zero (suc (suc (suc rest)))
  there :
    ∀ {index count} →
    WindowStart index count →
    WindowStart (suc index) (suc count)

windowLeftSlot :
  ∀ {index count} →
  WindowStart index count →
  Global.Slot index count
windowLeftSlot here =
  Global.here
windowLeftSlot (there start) =
  Global.there (windowLeftSlot start)

windowCenterSlot :
  ∀ {index count} →
  WindowStart index count →
  Global.Slot (suc index) count
windowCenterSlot here =
  Global.there Global.here
windowCenterSlot (there start) =
  Global.there (windowCenterSlot start)

windowRightSlot :
  ∀ {index count} →
  WindowStart index count →
  Global.Slot (suc (suc index)) count
windowRightSlot here =
  Global.there (Global.there Global.here)
windowRightSlot (there start) =
  Global.there (windowRightSlot start)

------------------------------------------------------------------------
-- Cell blocks inside one fixed-width row
------------------------------------------------------------------------

cellInRowRename :
  ∀ {machine cols index} →
  Global.Slot index cols →
  Fin.Fin (Canonical.CellWidth machine) →
  Fin.Fin
    (Decode.RowBitsWidth machine cols)
cellInRowRename {machine} {cols} =
  Global.blockRename {width = Canonical.CellWidth machine}

globalCellRename :
  ∀ {machine steps cols timeIndex cellIndex} →
  Global.Slot timeIndex (suc steps) →
  Global.Slot cellIndex cols →
  Fin.Fin (Canonical.CellWidth machine) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
globalCellRename {machine} {steps} {cols} rowSlot cellSlot i =
  Global.globalRowRename {machine} {steps} {cols} rowSlot
    (cellInRowRename {machine} {cols} cellSlot i)

------------------------------------------------------------------------
-- Six fixed cell blocks + shared selector
------------------------------------------------------------------------

sixCellGlobalRename :
  ∀ {machine steps cols timeIndex columnIndex} →
  Global.Slot timeIndex steps →
  WindowStart columnIndex cols →
  Fin.Fin (Canonical.WindowWidth machine) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
sixCellGlobalRename {machine} {steps} {cols} timeSlot start =
  Placement.finSumCases {m = cw} {n = cw + (cw + (cw + (cw + cw)))} {global = gw} oldLeft
    (Placement.finSumCases {m = cw} {n = cw + (cw + (cw + cw))} {global = gw} oldCenter
      (Placement.finSumCases {m = cw} {n = cw + (cw + cw)} {global = gw} oldRight
        (Placement.finSumCases {m = cw} {n = cw + cw} {global = gw} newLeft
          (Placement.finSumCases {m = cw} {n = cw} {global = gw} newCenter newRight))))
  where
    cw = Canonical.CellWidth machine
    gw = Trace.GlobalTraceWidth machine steps cols

    beforeSlot = Global.sameSlotInSucc timeSlot
    afterSlot = Global.nextSlotInSucc timeSlot

    oldLeft =
      globalCellRename {machine} {steps} {cols} beforeSlot (windowLeftSlot start)
    oldCenter =
      globalCellRename {machine} {steps} {cols} beforeSlot (windowCenterSlot start)
    oldRight =
      globalCellRename {machine} {steps} {cols} beforeSlot (windowRightSlot start)

    newLeft =
      globalCellRename {machine} {steps} {cols} afterSlot (windowLeftSlot start)
    newCenter =
      globalCellRename {machine} {steps} {cols} afterSlot (windowCenterSlot start)
    newRight =
      globalCellRename {machine} {steps} {cols} afterSlot (windowRightSlot start)

rawSelectedWindowRename :
  ∀ {machine steps cols timeIndex columnIndex} →
  Global.Slot timeIndex steps →
  WindowStart columnIndex cols →
  Fin.Fin (Selected.TransitionLocalWidth machine) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
rawSelectedWindowRename {machine} {steps} {cols} timeSlot start =
  Placement.finSumCases
    {m = Selector.RuleWidth machine}
    {n = Canonical.WindowWidth machine}
    {global = Trace.GlobalTraceWidth machine steps cols}
    (Global.globalSelectorRename {machine} {steps} {cols} timeSlot)
    (sixCellGlobalRename {machine} {steps} {cols} timeSlot start)

rawSelectedWindowBits :
  ∀ {machine steps cols timeIndex columnIndex} →
  Global.Slot timeIndex steps →
  WindowStart columnIndex cols →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols) →
  CNF.Bits (Selected.TransitionLocalWidth machine)
rawSelectedWindowBits {machine} {steps} {cols} timeSlot start globalBits =
  Rename.pullbackBits
    {local = Selected.TransitionLocalWidth machine}
    {global = Trace.GlobalTraceWidth machine steps cols}
    (rawSelectedWindowRename {machine} {steps} {cols} timeSlot start)
    globalBits

rawSelectedWindowPlacedPredicate :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : WindowStart columnIndex cols) →
  Placed.PlacedPredicate
    (Selected.TransitionLocalWidth machine)
    (Trace.GlobalTraceWidth machine steps cols)
rawSelectedWindowPlacedPredicate {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty timeSlot start =
  Placed.placed-predicate
    (rawSelectedWindowRename {machine} {steps} {cols} timeSlot start)
    (Selected.selectedRuleWindowPredicateWithCoverage {machine = machine}
      stateCoverage symbolCoverage nonempty)

rawSelectedWindowCNF :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : WindowStart columnIndex cols) →
  CNF.CNF (Trace.GlobalTraceWidth machine steps cols)
rawSelectedWindowCNF {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty timeSlot start =
  Placed.compilePlaced
    (rawSelectedWindowPlacedPredicate {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty timeSlot start)

rawSelectedWindowCNF_sound :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  CNF.evaluateCNF
    (rawSelectedWindowCNF {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty timeSlot start)
    globalBits
  ≡ true →
  Selected.selectedRuleWindowPredicateWithCoverage {machine = machine}
    stateCoverage symbolCoverage nonempty
    (rawSelectedWindowBits {machine} {steps} {cols} timeSlot start globalBits)
  ≡ true
rawSelectedWindowCNF_sound {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits accepted =
  Rename.placedTruthTableCNFSound
    (rawSelectedWindowRename {machine} {steps} {cols} timeSlot start)
    (Selected.selectedRuleWindowPredicateWithCoverage {machine = machine}
      stateCoverage symbolCoverage nonempty)
    globalBits
    accepted

rawSelectedWindowCNF_complete :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Selected.selectedRuleWindowPredicateWithCoverage {machine = machine}
    stateCoverage symbolCoverage nonempty
    (rawSelectedWindowBits {machine} {steps} {cols} timeSlot start globalBits)
  ≡ true →
  CNF.evaluateCNF
    (rawSelectedWindowCNF {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty timeSlot start)
    globalBits
  ≡ true
rawSelectedWindowCNF_complete {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits accepted =
  Rename.placedTruthTableCNFComplete
    (rawSelectedWindowRename {machine} {steps} {cols} timeSlot start)
    (Selected.selectedRuleWindowPredicateWithCoverage {machine = machine}
      stateCoverage symbolCoverage nonempty)
    globalBits
    accepted

record RawGlobalWindowCNFReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    fixedWindowCoordinatePaid : Bool
    sixCellRawGlobalPlacementPaid : Bool
    sharedSelectorRawPlacementPaid : Bool
    arbitraryBitsLocalDecodePaid : Bool
    rawWindowTruthTableCNFPaid : Bool
    rawWindowCNFSoundCompletePaid : Bool
    enumerateAllWindowCoordinatesPaid : Bool
    enumerateAllTimeCoordinatesPaid : Bool
    globalTransitionConjunctionPaid : Bool
    endpointCNFsPaid : Bool
    acceptingAssignmentIffRunPaid : Bool
    polynomialReductionPaid : Bool
    pVsNPResolved : Bool

rawGlobalWindowCNFReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  RawGlobalWindowCNFReceipt machine
rawGlobalWindowCNFReceipt machine = record
  { fixedWindowCoordinatePaid = true
  ; sixCellRawGlobalPlacementPaid = true
  ; sharedSelectorRawPlacementPaid = true
  ; arbitraryBitsLocalDecodePaid = true
  ; rawWindowTruthTableCNFPaid = true
  ; rawWindowCNFSoundCompletePaid = true
  ; enumerateAllWindowCoordinatesPaid = false
  ; enumerateAllTimeCoordinatesPaid = false
  ; globalTransitionConjunctionPaid = false
  ; endpointCNFsPaid = false
  ; acceptingAssignmentIffRunPaid = false
  ; polynomialReductionPaid = false
  ; pVsNPResolved = false
  }
