module DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact where

------------------------------------------------------------------------
-- ENUMERATE ALL FIXED (time,column) WINDOWS -> ONE GLOBAL TRANSITION CNF
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

record SomeSlot (count : Nat) : Set where
  constructor some-slot
  field
    index : Nat
    witness : Global.Slot index count

open SomeSlot public

shiftSomeSlot :
  ∀ {count} →
  SomeSlot count →
  SomeSlot (suc count)
shiftSomeSlot (some-slot index witness) =
  some-slot (suc index) (Global.there witness)

mapShiftSlots :
  ∀ {count} →
  List (SomeSlot count) →
  List (SomeSlot (suc count))
mapShiftSlots [] = []
mapShiftSlots (slot ∷ rest) =
  shiftSomeSlot slot ∷ mapShiftSlots rest

allSlots :
  (count : Nat) →
  List (SomeSlot count)
allSlots zero = []
allSlots (suc count) =
  some-slot zero Global.here
  ∷ mapShiftSlots (allSlots count)

record SomeWindowStart (cols : Nat) : Set where
  constructor some-window-start
  field
    index : Nat
    witness : Raw.WindowStart index cols

open SomeWindowStart public

shiftSomeWindowStart :
  ∀ {cols} →
  SomeWindowStart cols →
  SomeWindowStart (suc cols)
shiftSomeWindowStart (some-window-start index witness) =
  some-window-start (suc index) (Raw.there witness)

mapShiftWindowStarts :
  ∀ {cols} →
  List (SomeWindowStart cols) →
  List (SomeWindowStart (suc cols))
mapShiftWindowStarts [] = []
mapShiftWindowStarts (start ∷ rest) =
  shiftSomeWindowStart start ∷ mapShiftWindowStarts rest

allWindowStarts :
  (cols : Nat) →
  List (SomeWindowStart cols)
allWindowStarts zero = []
allWindowStarts (suc zero) = []
allWindowStarts (suc (suc zero)) = []
allWindowStarts (suc (suc (suc rest))) =
  some-window-start zero Raw.here
  ∷ mapShiftWindowStarts
      (allWindowStarts (suc (suc rest)))

predicatesForOneTime :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps) →
  List (SomeWindowStart cols) →
  List
    (Placed.PlacedPredicate
      (Selected.TransitionLocalWidth machine)
      (Trace.GlobalTraceWidth machine steps cols))
predicatesForOneTime
    stateCoverage symbolCoverage nonempty timeSlot [] =
  []
predicatesForOneTime
    stateCoverage symbolCoverage nonempty timeSlot
    (some-window-start columnIndex start ∷ rest) =
  Raw.rawSelectedWindowPlacedPredicate
    stateCoverage symbolCoverage nonempty timeSlot start
  ∷
  predicatesForOneTime
    stateCoverage symbolCoverage nonempty timeSlot rest

appendPredicates :
  ∀ {local global} →
  List (Placed.PlacedPredicate local global) →
  List (Placed.PlacedPredicate local global) →
  List (Placed.PlacedPredicate local global)
appendPredicates [] right = right
appendPredicates (x ∷ xs) right =
  x ∷ appendPredicates xs right

predicatesForAllTimes :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine) →
  List (SomeSlot steps) →
  List
    (Placed.PlacedPredicate
      (Selected.TransitionLocalWidth machine)
      (Trace.GlobalTraceWidth machine steps cols))
predicatesForAllTimes
    stateCoverage symbolCoverage nonempty [] =
  []
predicatesForAllTimes
    stateCoverage symbolCoverage nonempty
    (some-slot timeIndex timeSlot ∷ rest) =
  appendPredicates
    (predicatesForOneTime
      stateCoverage symbolCoverage nonempty timeSlot
      (allWindowStarts _))
    (predicatesForAllTimes
      stateCoverage symbolCoverage nonempty rest)

allGlobalTransitionPredicates :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat) →
  List
    (Placed.PlacedPredicate
      (Selected.TransitionLocalWidth machine)
      (Trace.GlobalTraceWidth machine steps cols))
allGlobalTransitionPredicates
    stateCoverage symbolCoverage nonempty steps cols =
  predicatesForAllTimes
    stateCoverage symbolCoverage nonempty
    (allSlots steps)

globalTransitionCNF :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat) →
  CNF.CNF (Trace.GlobalTraceWidth machine steps cols)
globalTransitionCNF
    stateCoverage symbolCoverage nonempty steps cols =
  Placed.compilePlacedAll
    (allGlobalTransitionPredicates
      stateCoverage symbolCoverage nonempty steps cols)

globalTransitionCNF_sound :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  CNF.evaluateCNF
    (globalTransitionCNF
      stateCoverage symbolCoverage nonempty steps cols)
    globalBits
  ≡ true →
  Placed.AllPlacedSatisfied globalBits
    (allGlobalTransitionPredicates
      stateCoverage symbolCoverage nonempty steps cols)
globalTransitionCNF_sound
    stateCoverage symbolCoverage nonempty
    steps cols globalBits accepted =
  Placed.compilePlacedAllSound
    (allGlobalTransitionPredicates
      stateCoverage symbolCoverage nonempty steps cols)
    globalBits accepted

globalTransitionCNF_complete :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Placed.AllPlacedSatisfied globalBits
    (allGlobalTransitionPredicates
      stateCoverage symbolCoverage nonempty steps cols) →
  CNF.evaluateCNF
    (globalTransitionCNF
      stateCoverage symbolCoverage nonempty steps cols)
    globalBits
  ≡ true
globalTransitionCNF_complete
    stateCoverage symbolCoverage nonempty
    steps cols globalBits allSatisfied =
  Placed.compilePlacedAllComplete
    (allGlobalTransitionPredicates
      stateCoverage symbolCoverage nonempty steps cols)
    globalBits allSatisfied

record GlobalTransitionConjunctionReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    enumerateTimeSlotsPaid : Bool
    enumerateWindowStartsPaid : Bool
    cartesianTransitionCoordinatesPaid : Bool
    oneGlobalTransitionCNFPaid : Bool
    conjunctionSoundPaid : Bool
    conjunctionCompletePaid : Bool
    endpointCNFsPaid : Bool
    satisfyingAssignmentIffRunPaid : Bool
    polynomialClauseCountPaid : Bool
    polynomialReductionPaid : Bool
    pVsNPResolved : Bool

globalTransitionConjunctionReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  GlobalTransitionConjunctionReceipt machine
globalTransitionConjunctionReceipt machine = record
  { enumerateTimeSlotsPaid = true
  ; enumerateWindowStartsPaid = true
  ; cartesianTransitionCoordinatesPaid = true
  ; oneGlobalTransitionCNFPaid = true
  ; conjunctionSoundPaid = true
  ; conjunctionCompletePaid = true
  ; endpointCNFsPaid = false
  ; satisfyingAssignmentIffRunPaid = false
  ; polynomialClauseCountPaid = false
  ; polynomialReductionPaid = false
  ; pVsNPResolved = false
  }
