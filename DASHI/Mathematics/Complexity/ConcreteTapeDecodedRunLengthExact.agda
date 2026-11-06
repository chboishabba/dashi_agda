module DASHI.Mathematics.Complexity.ConcreteTapeDecodedRunLengthExact where

------------------------------------------------------------------------
-- THE P4 DECODED RUN HAS EXACTLY THE REQUESTED NUMBER OF STEPS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong; subst)

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
      Scan.AllTimesSemantic {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits
        (first ∷ rest))
    (ordered : Induction.OrderedSlotChain (first ∷ rest))
    (unique :
      WF.ExactlyOneHead
        (Local.cells {machine}
          (Step.decodedBeforeRow {machine} {steps} {cols}
            stateCoverage symbolCoverage
            (Transition.witness first) globalBits)))
    (margin :
      Margin.HeadMargin (suc (Induction.timesLength (first ∷ rest)))
        (Local.cells {machine}
          (Step.decodedBeforeRow {machine} {steps} {cols}
            stateCoverage symbolCoverage
            (Transition.witness first) globalBits)))
    (guards :
      Step.AllTimeStepsBoundaryGuards {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits) →
  Run.runLength
    (Induction.run
      (Induction.buildDecodedRunNonempty {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits
        first rest semantic ordered unique margin guards))
  ≡ Induction.timesLength (first ∷ rest)
buildDecodedRunNonempty_length
    stateCoverage symbolCoverage nonempty globalBits
    first []
    (Scan.semanticTimesStep current Scan.semanticTimesDone)
    Induction.orderedOne
    unique margin guards =
  refl
buildDecodedRunNonempty_length {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits
    first (second ∷ rest)
    (Scan.semanticTimesStep current remaining)
    (Induction.orderedCons adjacent orderedRest)
    unique margin guards =
  cong suc
    (trans
      (transportRunStart_length
        afterEq
        (Induction.run recursive))
      (buildDecodedRunNonempty_length {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits
        second rest remaining orderedRest
        nextUnique nextMargin guards))
  where
    interior =
      Margin.interiorFromUniqueMargin {machine}
        unique (Induction.weakenMarginToOne margin)

    step =
      Step.decodedAdjacentRowsFormMachineStep {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty
        (Transition.witness first) globalBits
        interior current
        (guards (Transition.witness first) interior current)

    afterEq =
      Induction.adjacentDecodedRows {machine} {steps} {cols}
        stateCoverage symbolCoverage adjacent globalBits

    nextUnique =
      Induction.transportUniqueRow afterEq
        (WF.afterExactlyOneHead step)

    nextMargin =
      Induction.transportMarginRow afterEq
        (Margin.wellFormedStepMargin step margin)

    recursive =
      Induction.buildDecodedRunNonempty {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits
        second rest remaining orderedRest
        nextUnique nextMargin guards

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
      Scan.AllTimesSemantic {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits
        (Transition.allSlots steps))
    (startUnique :
      WF.ExactlyOneHead
        (Local.cells {machine}
          (Decode.decodeRow stateCoverage symbolCoverage cols
            (Global.rowSliceBits {machine} {steps} {cols}
              (Global.here {remaining = steps})
              globalBits))))
    (startMargin :
      Margin.HeadMargin (suc steps)
        (Local.cells {machine}
          (Decode.decodeRow stateCoverage symbolCoverage cols
            (Global.rowSliceBits {machine} {steps} {cols}
              (Global.here {remaining = steps})
              globalBits))))
    (guards :
      Step.AllTimeStepsBoundaryGuards {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits) →
  Run.runLength
    (Induction.run
      (Induction.decodedAllSlotsRun {machine} {cols}
        stateCoverage symbolCoverage nonempty
        steps globalBits semantic startUnique startMargin guards))
  ≡ steps
decodedAllSlotsRun_length
    stateCoverage symbolCoverage nonempty
    zero globalBits Scan.semanticTimesDone
    startUnique startMargin guards =
  refl
decodedAllSlotsRun_length {machine} {cols}
    stateCoverage symbolCoverage nonempty
    (suc steps) globalBits semantic
    startUnique startMargin guards =
  trans
    (buildDecodedRunNonempty_length {machine} {suc steps} {cols}
      stateCoverage symbolCoverage nonempty globalBits
      (Transition.some-slot zero (Global.here {remaining = steps}))
      (Transition.mapShiftSlots (Transition.allSlots steps))
      semantic
      (Induction.allSlotsOrdered (suc steps))
      startUnique
      (subst (λ len → Margin.HeadMargin len (Local.cells {machine} (Decode.decodeRow stateCoverage symbolCoverage cols (Global.rowSliceBits {machine} {suc steps} {cols} (Global.here {remaining = suc steps}) globalBits))))
             (cong suc (sym (Induction.allSlotsLength (suc steps))))
             startMargin)
      guards)
    (Induction.allSlotsLength (suc steps))
