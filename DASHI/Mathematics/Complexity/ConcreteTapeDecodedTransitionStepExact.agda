module DASHI.Mathematics.Complexity.ConcreteTapeDecodedTransitionStepExact where

------------------------------------------------------------------------
-- ONE SAT TIME SLICE -> ACTUAL WELL-FORMED MACHINE STEP
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans; sym)

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
import DASHI.Mathematics.Complexity.ConcreteTapeAfterUniqueFromLocalityExact as AfterUnique
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

decodedBeforeRow :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Local.TapeRow machine
decodedBeforeRow stateCoverage symbolCoverage timeSlot globalBits =
  Decode.decodeRow stateCoverage symbolCoverage _
    (Global.rowSliceBits
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
decodedAfterRow stateCoverage symbolCoverage timeSlot globalBits =
  Decode.decodeRow stateCoverage symbolCoverage _
    (Global.rowSliceBits
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
      (decodedBeforeRow
        stateCoverage symbolCoverage timeSlot globalBits))
  ≡
  Coordinate.listLength
    (Local.cells
      (decodedAfterRow
        stateCoverage symbolCoverage timeSlot globalBits))
decodedRowsSameLength
    {cols = cols}
    stateCoverage symbolCoverage timeSlot globalBits =
  trans
    (Decode.decodeCellsLength stateCoverage symbolCoverage cols
      (Global.rowSliceBits
        (Global.sameSlotInSucc timeSlot) globalBits))
    (sym
      (Decode.decodeCellsLength stateCoverage symbolCoverage cols
        (Global.rowSliceBits
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
    (WholeDecoded.ruleAtTime nonempty timeSlot globalBits)
    (decodedBeforeRow
      stateCoverage symbolCoverage timeSlot globalBits)
    (decodedAfterRow
      stateCoverage symbolCoverage timeSlot globalBits)
decodedTimeLocalityScan
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits semantics =
  record
    { Character.ruleOccursInMachine =
        Selector.decodeRuleOccurs nonempty
          (Global.selectorSliceBits timeSlot globalBits)
    ; Character.sameRowLength =
        decodedRowsSameLength
          stateCoverage symbolCoverage timeSlot globalBits
    ; Character.everyWindowLegal =
        WholeDecoded.allRawWindowsSemanticToDecodedAllWindowsLegal
          stateCoverage symbolCoverage nonempty
          timeSlot globalBits semantics
    }

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
        (decodedBeforeRow
          stateCoverage symbolCoverage timeSlot globalBits)) →
  Scan.AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits
    (Transition.allWindowStarts cols) →
  WF.WellFormedMachineStep machine
    (decodedBeforeRow
      stateCoverage symbolCoverage timeSlot globalBits)
    (decodedAfterRow
      stateCoverage symbolCoverage timeSlot globalBits)
decodedAdjacentRowsFormMachineStep
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits interior semantics =
  AfterUnique.localityScanWithInteriorGivesWellFormedStep
    (decodedTimeLocalityScan
      stateCoverage symbolCoverage nonempty
      timeSlot globalBits semantics)
    interior

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
        (decodedBeforeRow
          stateCoverage symbolCoverage timeSlot globalBits))
    (semantics :
      Scan.AllRawWindowsSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot globalBits
        (Transition.allWindowStarts cols)) →
  WF.ExactlyOneHead
    (Local.cells
      (decodedAfterRow
        stateCoverage symbolCoverage timeSlot globalBits))
decodedStepAfterUnique
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits interior semantics =
  WF.afterExactlyOneHead
    (decodedAdjacentRowsFormMachineStep
      stateCoverage symbolCoverage nonempty
      timeSlot globalBits interior semantics)

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
