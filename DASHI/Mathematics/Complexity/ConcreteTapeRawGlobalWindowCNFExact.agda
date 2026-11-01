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

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
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
    (DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact.RowBitsWidth
      machine cols)
cellInRowRename =
  Global.blockRename

globalCellRename :
  ∀ {machine steps cols timeIndex cellIndex} →
  Global.Slot timeIndex (suc steps) →
  Global.Slot cellIndex cols →
  Fin.Fin (Canonical.CellWidth machine) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
globalCellRename rowSlot cellSlot i =
  Global.globalRowRename rowSlot
    (cellInRowRename cellSlot i)

------------------------------------------------------------------------
-- Six fixed cell blocks + shared selector
------------------------------------------------------------------------

sixCellGlobalRename :
  ∀ {machine steps cols timeIndex columnIndex} →
  Global.Slot timeIndex steps →
  WindowStart columnIndex cols →
  Fin.Fin (Canonical.WindowWidth machine) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
sixCellGlobalRename timeSlot start =
  Placement.finSumCases oldLeft
    (Placement.finSumCases oldCenter
      (Placement.finSumCases oldRight
        (Placement.finSumCases newLeft
          (Placement.finSumCases newCenter newRight))))
  where
    beforeSlot = Global.sameSlotInSucc timeSlot
    afterSlot = Global.nextSlotInSucc timeSlot

    oldLeft =
      globalCellRename beforeSlot (windowLeftSlot start)
    oldCenter =
      globalCellRename beforeSlot (windowCenterSlot start)
    oldRight =
      globalCellRename beforeSlot (windowRightSlot start)

    newLeft =
      globalCellRename afterSlot (windowLeftSlot start)
    newCenter =
      globalCellRename afterSlot (windowCenterSlot start)
    newRight =
      globalCellRename afterSlot (windowRightSlot start)

rawSelectedWindowRename :
  ∀ {machine steps cols timeIndex columnIndex} →
  Global.Slot timeIndex steps →
  WindowStart columnIndex cols →
  Fin.Fin (Selected.TransitionLocalWidth machine) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
rawSelectedWindowRename timeSlot start =
  Placement.finSumCases
    (Global.globalSelectorRename timeSlot)
    (sixCellGlobalRename timeSlot start)

rawSelectedWindowBits :
  ∀ {machine steps cols timeIndex columnIndex} →
  Global.Slot timeIndex steps →
  WindowStart columnIndex cols →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols) →
  CNF.Bits (Selected.TransitionLocalWidth machine)
rawSelectedWindowBits timeSlot start globalBits =
  Rename.pullbackBits
    (rawSelectedWindowRename timeSlot start)
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
rawSelectedWindowPlacedPredicate
    stateCoverage symbolCoverage nonempty timeSlot start =
  Placed.placed-predicate
    (rawSelectedWindowRename timeSlot start)
    (Selected.selectedRuleWindowPredicateWithCoverage
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
rawSelectedWindowCNF
    stateCoverage symbolCoverage nonempty timeSlot start =
  Placed.compilePlaced
    (rawSelectedWindowPlacedPredicate
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
    (rawSelectedWindowCNF
      stateCoverage symbolCoverage nonempty timeSlot start)
    globalBits
  ≡ true →
  Selected.selectedRuleWindowPredicateWithCoverage
    stateCoverage symbolCoverage nonempty
    (rawSelectedWindowBits timeSlot start globalBits)
  ≡ true
rawSelectedWindowCNF_sound
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits accepted =
  Rename.placedTruthTableCNFSound
    (rawSelectedWindowRename timeSlot start)
    (Selected.selectedRuleWindowPredicateWithCoverage
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
  Selected.selectedRuleWindowPredicateWithCoverage
    stateCoverage symbolCoverage nonempty
    (rawSelectedWindowBits timeSlot start globalBits)
  ≡ true →
  CNF.evaluateCNF
    (rawSelectedWindowCNF
      stateCoverage symbolCoverage nonempty timeSlot start)
    globalBits
  ≡ true
rawSelectedWindowCNF_complete
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits accepted =
  Rename.placedTruthTableCNFComplete
    (rawSelectedWindowRename timeSlot start)
    (Selected.selectedRuleWindowPredicateWithCoverage
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
