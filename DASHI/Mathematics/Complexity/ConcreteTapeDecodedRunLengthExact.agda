module DASHI.Mathematics.Complexity.ConcreteTapeDecodedRunLengthExact where

------------------------------------------------------------------------
-- THE P4 DECODED RUN HAS EXACTLY THE REQUESTED NUMBER OF STEPS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedTransitionStepExact as Step
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedRunInductionExact as Induction
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

transportRunStart_length :
  ∀ {machine}
    {left right finish : Local.TapeRow machine}
    {rows : List (Local.TapeRow machine)}
    (eq : left ≡ right)
    (run : Run.WellFormedTapeRun machine right rows finish) →
  Run.runLength (Induction.transportRunStart eq run)
  ≡ Run.runLength run
transportRunStart_length refl run =
  refl

buildDecodedRunNonempty_length :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (first : Transition.SomeSlot steps)
    (rest : List (Transition.SomeSlot steps))
    (semantic :
      Scan.AllTimesSemantic
        stateCoverage symbolCoverage nonempty globalBits
        (first ∷ rest))
    (ordered : Induction.OrderedSlotChain (first ∷ rest))
    (unique :
      WF.ExactlyOneHead
        (Local.cells
          (Step.decodedBeforeRow
            stateCoverage symbolCoverage
            (Transition.witness first) globalBits)))
    (margin :
      Margin.HeadMargin (suc (Induction.timesLength (first ∷ rest)))
        (Local.cells
          (Step.decodedBeforeRow
            stateCoverage symbolCoverage
            (Transition.witness first) globalBits))) →
  Run.runLength
    (Induction.run
      (Induction.buildDecodedRunNonempty
        stateCoverage symbolCoverage nonempty globalBits
        first rest semantic ordered unique margin))
  ≡ Induction.timesLength (first ∷ rest)
buildDecodedRunNonempty_length
    stateCoverage symbolCoverage nonempty globalBits
    first []
    (Scan.semanticTimesStep current Scan.semanticTimesDone)
    Induction.orderedOne
    unique margin =
  refl
buildDecodedRunNonempty_length
    stateCoverage symbolCoverage nonempty globalBits
    first (second ∷ rest)
    (Scan.semanticTimesStep current remaining)
    (Induction.orderedCons adjacent orderedRest)
    unique margin
    rewrite transportRunStart_length
      (Induction.adjacentDecodedRows
        stateCoverage symbolCoverage adjacent globalBits)
      (Induction.run recursive)
          | buildDecodedRunNonempty_length
              stateCoverage symbolCoverage nonempty globalBits
              second rest remaining orderedRest
              nextUnique nextMargin =
  refl
  where
    interior =
      Margin.interiorFromUniqueMargin
        unique (Induction.weakenMarginToOne margin)

    step =
      Step.decodedAdjacentRowsFormMachineStep
        stateCoverage symbolCoverage nonempty
        (Transition.witness first) globalBits
        interior current

    afterEq =
      Induction.adjacentDecodedRows
        stateCoverage symbolCoverage adjacent globalBits

    nextUnique =
      Induction.transportUniqueRow afterEq
        (WF.afterExactlyOneHead step)

    nextMargin =
      Induction.transportMarginRow afterEq
        (Margin.wellFormedStepMargin step margin)

    recursive =
      Induction.buildDecodedRunNonempty
        stateCoverage symbolCoverage nonempty globalBits
        second rest remaining orderedRest
        nextUnique nextMargin

decodedAllSlotsRun_length :
  ∀ {machine cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps : Nat)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (semantic :
      Scan.AllTimesSemantic
        stateCoverage symbolCoverage nonempty globalBits
        (Transition.allSlots steps))
    (startUnique :
      WF.ExactlyOneHead
        (Local.cells
          (Decode.decodeRow
            stateCoverage symbolCoverage cols
            (Global.rowSliceBits
              (Global.here {remaining = steps})
              globalBits))))
    (startMargin :
      Margin.HeadMargin (suc steps)
        (Local.cells
          (Decode.decodeRow
            stateCoverage symbolCoverage cols
            (Global.rowSliceBits
              (Global.here {remaining = steps})
              globalBits)))) →
  Run.runLength
    (Induction.run
      (Induction.decodedAllSlotsRun
        stateCoverage symbolCoverage nonempty
        steps globalBits semantic startUnique startMargin))
  ≡ steps
decodedAllSlotsRun_length
    stateCoverage symbolCoverage nonempty
    zero globalBits Scan.semanticTimesDone
    startUnique startMargin =
  refl
decodedAllSlotsRun_length
    stateCoverage symbolCoverage nonempty
    (suc steps) globalBits semantic
    startUnique startMargin
    rewrite sym (Induction.allSlotsLength (suc steps))
          | buildDecodedRunNonempty_length
              stateCoverage symbolCoverage nonempty globalBits
              (Transition.some-slot zero Global.here)
              (Transition.mapShiftSlots (Transition.allSlots steps))
              semantic
              (Induction.allSlotsOrdered (suc steps))
              startUnique startMargin =
  Induction.allSlotsLength (suc steps)
