module DASHI.Mathematics.Complexity.ConcreteTapeDecodedTransitionStepExact where

------------------------------------------------------------------------
-- ONE SAT TIME SLICE -> ACTUAL WELL-FORMED MACHINE STEP
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedWholeRowSemanticExact as WholeDecoded
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeCenteredWindowExtractionExact as Center
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeAfterUniqueFromLocalityExact as AfterUnique
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

canonicalListLength_eq_coordinate :
  ∀ {A : Set} (xs : List A) →
  Canonical.listLength xs ≡ Coordinate.listLength xs
canonicalListLength_eq_coordinate [] = refl
canonicalListLength_eq_coordinate (_ ∷ xs) =
  cong suc (canonicalListLength_eq_coordinate xs)

decodeCellsCoordinateLength :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (count : Nat)
    (bits : CNF.Bits (Decode.RowBitsWidth machine count)) →
  Coordinate.listLength
    (Decode.decodeCells {machine} stateCoverage symbolCoverage count bits)
  ≡ count
decodeCellsCoordinateLength {machine} stateCoverage symbolCoverage count bits =
  trans
    (sym (canonicalListLength_eq_coordinate (Decode.decodeCells {machine} stateCoverage symbolCoverage count bits)))
    (Decode.decodeCellsLength {machine} stateCoverage symbolCoverage count bits)

decodedBeforeRow :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Local.TapeRow machine
decodedBeforeRow {machine} {steps} {cols} stateCoverage symbolCoverage timeSlot globalBits =
  Decode.decodeRow stateCoverage symbolCoverage cols
    (Global.rowSliceBits {machine} {steps} {cols}
      (Global.sameSlotInSucc timeSlot) globalBits)

decodedAfterRow :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Local.TapeRow machine
decodedAfterRow {machine} {steps} {cols} stateCoverage symbolCoverage timeSlot globalBits =
  Decode.decodeRow stateCoverage symbolCoverage cols
    (Global.rowSliceBits {machine} {steps} {cols}
      (Global.nextSlotInSucc timeSlot) globalBits)

decodedRowsSameLength :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Coordinate.listLength
    (Local.cells
      (decodedBeforeRow {machine} {steps} {cols}
        stateCoverage symbolCoverage timeSlot globalBits))
  ≡
  Coordinate.listLength
    (Local.cells
      (decodedAfterRow {machine} {steps} {cols}
        stateCoverage symbolCoverage timeSlot globalBits))
decodedRowsSameLength
    {machine} {steps} {cols}
    stateCoverage symbolCoverage timeSlot globalBits =
  trans
    (decodeCellsCoordinateLength {machine} stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.sameSlotInSucc timeSlot) globalBits))
    (sym
      (decodeCellsCoordinateLength {machine} stateCoverage symbolCoverage cols
        (Global.rowSliceBits {machine} {steps} {cols}
          (Global.nextSlotInSucc timeSlot) globalBits)))

decodedTimeLocalityScan :
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
  Character.TransitionLocalityScan machine
    (WholeDecoded.ruleAtTime {machine} {steps} {cols} nonempty timeSlot globalBits)
    (decodedBeforeRow {machine} {steps} {cols}
      stateCoverage symbolCoverage timeSlot globalBits)
    (decodedAfterRow {machine} {steps} {cols}
      stateCoverage symbolCoverage timeSlot globalBits)
decodedTimeLocalityScan {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits semantics =
  record
    { ruleOccursInMachine =
        Selector.decodeRuleOccurs nonempty
          (Global.selectorSliceBits {machine} {steps} {cols} timeSlot globalBits)
    ; sameRowLength =
        decodedRowsSameLength {machine} {steps} {cols}
          stateCoverage symbolCoverage timeSlot globalBits
    ; everyWindowLegal =
        WholeDecoded.allRawWindowsSemanticToDecodedAllWindowsLegal {machine} {steps} {cols}
          stateCoverage symbolCoverage nonempty
          timeSlot globalBits semantics
    }

StepBoundaryGuards :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (interior :
      Character.InteriorHeadConfiguration machine
        (decodedBeforeRow {machine} {steps} {cols}
          stateCoverage symbolCoverage timeSlot globalBits))
    (semantics :
      Scan.AllRawWindowsSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot globalBits
        (Transition.allWindowStarts cols)) →
    Set
StepBoundaryGuards {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits interior semantics =
  Pattern.FrontPlain
    (Center.afterPrefix
      (Center.centeredOccurrenceFromGlobalScan
        (Character.localityScanToGlobalTransitionScan
          (decodedTimeLocalityScan {machine} {steps} {cols}
            stateCoverage symbolCoverage nonempty
            timeSlot globalBits semantics)
          interior)))
  ×
  Pattern.EndPlain
    (Center.afterSuffix
      (Center.centeredOccurrenceFromGlobalScan
        (Character.localityScanToGlobalTransitionScan
          (decodedTimeLocalityScan {machine} {steps} {cols}
            stateCoverage symbolCoverage nonempty
            timeSlot globalBits semantics)
          interior)))

AllTimeStepsBoundaryGuards :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Set
AllTimeStepsBoundaryGuards {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits =
  ∀ {timeIndex} (timeSlot : Global.Slot timeIndex steps)
    (interior :
      Character.InteriorHeadConfiguration machine
        (decodedBeforeRow {machine} {steps} {cols}
          stateCoverage symbolCoverage timeSlot globalBits))
    (semantics :
      Scan.AllRawWindowsSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot globalBits
        (Transition.allWindowStarts cols)) →
  StepBoundaryGuards
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits interior semantics

decodedAdjacentRowsFormMachineStep :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (interior :
      Character.InteriorHeadConfiguration machine
        (decodedBeforeRow {machine} {steps} {cols}
          stateCoverage symbolCoverage timeSlot globalBits))
    (semantics :
      Scan.AllRawWindowsSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot globalBits
        (Transition.allWindowStarts cols)) →
  StepBoundaryGuards
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits interior semantics →
  WF.WellFormedMachineStep machine
    (decodedBeforeRow {machine} {steps} {cols}
      stateCoverage symbolCoverage timeSlot globalBits)
    (decodedAfterRow {machine} {steps} {cols}
      stateCoverage symbolCoverage timeSlot globalBits)
decodedAdjacentRowsFormMachineStep {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits interior semantics (frontGuard , endGuard) =
  AfterUnique.localityScanWithInteriorGivesWellFormedStep {machine}
    (decodedTimeLocalityScan {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty
      timeSlot globalBits semantics)
    interior frontGuard endGuard

decodedStepAfterUnique :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (interior :
      Character.InteriorHeadConfiguration machine
        (decodedBeforeRow {machine} {steps} {cols}
          stateCoverage symbolCoverage timeSlot globalBits))
    (semantics :
      Scan.AllRawWindowsSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot globalBits
        (Transition.allWindowStarts cols)) →
  StepBoundaryGuards
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits interior semantics →
  WF.ExactlyOneHead
    (Local.cells
      (decodedAfterRow {machine} {steps} {cols}
        stateCoverage symbolCoverage timeSlot globalBits))
decodedStepAfterUnique {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits interior semantics guards =
  WF.afterExactlyOneHead
    (decodedAdjacentRowsFormMachineStep {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty
      timeSlot globalBits interior semantics guards)

record DecodedTransitionStepReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    decodedRowsSameLengthPaid : Bool
    decodedSelectorOccursPaid : Bool
    decodedAllWindowsLegalPaid : Bool
    localityAfterUniqueDerivedPaid : Bool
    oneSATTimeSliceToMachineStepPaid : Bool

decodedTransitionStepReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  DecodedTransitionStepReceipt machine
decodedTransitionStepReceipt machine = record
  { decodedRowsSameLengthPaid = true
  ; decodedSelectorOccursPaid = true
  ; decodedAllWindowsLegalPaid = true
  ; localityAfterUniqueDerivedPaid = true
  ; oneSATTimeSliceToMachineStepPaid = true
  }
