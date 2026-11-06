module DASHI.Mathematics.Complexity.ConcreteTapeDecodedRunInductionExact where

------------------------------------------------------------------------
-- P4: ORDERED SAT TIME SLICES -> ACTUAL WellFormedTapeRun
--
-- allSlots T is the ordered list 0,...,T-1. Adjacent slots literally share
-- the same row block: the after row of t is the before row of t+1.
--
-- A head margin of 1 + number-of-remaining-steps is threaded through P3.
-- Each radius-one step consumes at most one margin cell. Consequently the
-- final row still has margin 1 and remains an interior one-head row.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedTransitionStepExact as Step
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

timesLength :
  ∀ {steps} → List (Transition.SomeSlot steps) → Nat
timesLength [] = zero
timesLength (_ ∷ rest) = suc (timesLength rest)

mapShiftSlotsLength :
  ∀ {steps}
    (times : List (Transition.SomeSlot steps)) →
  timesLength (Transition.mapShiftSlots times)
  ≡ timesLength times
mapShiftSlotsLength [] = refl
mapShiftSlotsLength (x ∷ xs)
  rewrite mapShiftSlotsLength xs =
  refl

allSlotsLength :
  (steps : Nat) →
  timesLength (Transition.allSlots steps) ≡ steps
allSlotsLength zero = refl
allSlotsLength (suc steps)
  rewrite mapShiftSlotsLength (Transition.allSlots steps)
        | allSlotsLength steps =
  refl

record AdjacentSlots
    {steps : Nat}
    (left right : Transition.SomeSlot steps) : Set₁ where
  field
    sameSharedRowBlock :
      ∀ {width : Nat} (i : Fin.Fin width) →
      Global.blockRename
        (Global.nextSlotInSucc (Transition.witness left)) i
      ≡
      Global.blockRename
        (Global.sameSlotInSucc (Transition.witness right)) i

open AdjacentSlots public

adjacentHereShiftHere :
  ∀ {steps} →
  AdjacentSlots
    (Transition.some-slot zero
      (Global.here {remaining = suc steps}))
    (Transition.shiftSomeSlot
      (Transition.some-slot zero
        (Global.here {remaining = steps})))
adjacentHereShiftHere =
  record { sameSharedRowBlock = λ i → refl }

shiftAdjacentSlots :
  ∀ {steps}
    {left right : Transition.SomeSlot steps} →
  AdjacentSlots left right →
  AdjacentSlots
    (Transition.shiftSomeSlot left)
    (Transition.shiftSomeSlot right)
shiftAdjacentSlots adjacency =
  record
    { sameSharedRowBlock =
        λ {width} i →
          cong (Placement.finRight width)
            (sameSharedRowBlock adjacency i)
    }

data OrderedSlotChain {steps : Nat} :
    List (Transition.SomeSlot steps) → Set₁ where
  orderedNil :
    OrderedSlotChain []
  orderedOne :
    ∀ {slot} →
    OrderedSlotChain (slot ∷ [])
  orderedCons :
    ∀ {left right rest} →
    AdjacentSlots left right →
    OrderedSlotChain (right ∷ rest) →
    OrderedSlotChain (left ∷ right ∷ rest)

shiftOrderedSlotChain :
  ∀ {steps}
    {times : List (Transition.SomeSlot steps)} →
  OrderedSlotChain times →
  OrderedSlotChain (Transition.mapShiftSlots times)
shiftOrderedSlotChain orderedNil =
  orderedNil
shiftOrderedSlotChain orderedOne =
  orderedOne
shiftOrderedSlotChain
    (orderedCons adjacent rest) =
  orderedCons
    (shiftAdjacentSlots adjacent)
    (shiftOrderedSlotChain rest)

allSlotsOrdered :
  (steps : Nat) →
  OrderedSlotChain (Transition.allSlots steps)
allSlotsOrdered zero =
  orderedNil
allSlotsOrdered (suc zero) =
  orderedOne
allSlotsOrdered (suc (suc steps)) =
  orderedCons
    adjacentHereShiftHere
    (shiftOrderedSlotChain
      (allSlotsOrdered (suc steps)))

adjacentRowSliceBits :
  ∀ {machine steps cols}
    {left right : Transition.SomeSlot steps} →
  AdjacentSlots left right →
  (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Global.rowSliceBits {machine} {steps} {cols}
    (Global.nextSlotInSucc (Transition.witness left))
    globalBits
  ≡
  Global.rowSliceBits {machine} {steps} {cols}
    (Global.sameSlotInSucc (Transition.witness right))
    globalBits
adjacentRowSliceBits {machine} {steps} {cols} {left = left} {right = right}
    adjacency globalBits =
  Placement.bitsExt pointwise
  where
    pointwise :
      ∀ (i : Fin.Fin (Decode.RowBitsWidth machine cols)) →
      CNF.lookupBit
        (Global.rowSliceBits {machine} {steps} {cols}
          (Global.nextSlotInSucc
            (Transition.witness left))
          globalBits) i
      ≡
      CNF.lookupBit
        (Global.rowSliceBits {machine} {steps} {cols}
          (Global.sameSlotInSucc
            (Transition.witness right))
          globalBits) i
    pointwise i =
      trans
        (Rename.pullbackLookup
          (Global.globalRowRename {machine} {steps} {cols}
            (Global.nextSlotInSucc
              (Transition.witness left)))
          globalBits i)
        (trans
          (cong (CNF.lookupBit globalBits)
            (cong Placement.finLeft
              (sameSharedRowBlock adjacency i)))
          (sym
            (Rename.pullbackLookup
              (Global.globalRowRename {machine} {steps} {cols}
                (Global.sameSlotInSucc
                  (Transition.witness right)))
              globalBits i)))

adjacentDecodedRows :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {left right : Transition.SomeSlot steps} →
  AdjacentSlots left right →
  (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Step.decodedAfterRow {machine} {steps} {cols}
      stateCoverage symbolCoverage
      (Transition.witness left) globalBits
  ≡
  Step.decodedBeforeRow {machine} {steps} {cols}
      stateCoverage symbolCoverage
      (Transition.witness right) globalBits
adjacentDecodedRows {machine} {steps} {cols} stateCoverage symbolCoverage
    adjacency globalBits =
  cong
    (Decode.decodeRow stateCoverage symbolCoverage cols)
    (adjacentRowSliceBits {machine} {steps} {cols} adjacency globalBits)

transportMarginRow :
  ∀ {machine k}
    {left right : Local.TapeRow machine} →
  left ≡ right →
  Margin.HeadMargin k (Local.cells left) →
  Margin.HeadMargin k (Local.cells right)
transportMarginRow refl margin = margin

transportUniqueRow :
  ∀ {machine}
    {left right : Local.TapeRow machine} →
  left ≡ right →
  WF.ExactlyOneHead (Local.cells left) →
  WF.ExactlyOneHead (Local.cells right)
transportUniqueRow refl unique = unique

transportRunStart :
  ∀ {machine}
    {left right finish : Local.TapeRow machine}
    {rows : List (Local.TapeRow machine)} →
  left ≡ right →
  Run.WellFormedTapeRun machine right rows finish →
  Run.WellFormedTapeRun machine left rows finish
transportRunStart refl run = run

weakenMarginToOne :
  ∀ {State Symbol : Set}
    {k : Nat}
    {cells : List (Local.TapeCell State Symbol)} →
  Margin.HeadMargin (suc k) cells →
  Margin.HeadMargin 1 cells
weakenMarginToOne {k = zero} margin =
  margin
weakenMarginToOne {k = suc k} margin =
  weakenMarginToOne (Margin.weakenMargin margin)

record DecodedRunResult
    {machine : Local.ConcreteTapeMachine}
    (start : Local.TapeRow machine) : Set₁ where
  field
    rows : List (Local.TapeRow machine)
    finish : Local.TapeRow machine
    run :
      Run.WellFormedTapeRun machine start rows finish
    finalUnique :
      WF.ExactlyOneHead (Local.cells finish)
    finalMargin :
      Margin.HeadMargin 1 (Local.cells finish)
    finalInterior :
      Character.InteriorHeadConfiguration machine finish

open DecodedRunResult public

buildDecodedRunNonempty :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (first : Transition.SomeSlot steps)
    (rest : List (Transition.SomeSlot steps)) →
  Scan.AllTimesSemantic {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits
    (first ∷ rest) →
  OrderedSlotChain (first ∷ rest) →
  WF.ExactlyOneHead
    (Local.cells
      (Step.decodedBeforeRow {machine} {steps} {cols} stateCoverage symbolCoverage
        (Transition.witness first) globalBits)) →
  Margin.HeadMargin (suc (timesLength (first ∷ rest)))
    (Local.cells
      (Step.decodedBeforeRow {machine} {steps} {cols} stateCoverage symbolCoverage
        (Transition.witness first) globalBits)) →
  Step.AllTimeStepsBoundaryGuards {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits →
  DecodedRunResult {machine = machine}
    (Step.decodedBeforeRow {machine} {steps} {cols} stateCoverage symbolCoverage
      (Transition.witness first) globalBits)
buildDecodedRunNonempty
    stateCoverage symbolCoverage nonempty globalBits
    first []
    (Scan.semanticTimesStep current Scan.semanticTimesDone)
    orderedOne
    unique margin guards =
  record
    { rows = after ∷ []
    ; finish = after
    ; run =
        Run.runStep step Run.runDone
    ; finalUnique =
        WF.afterExactlyOneHead step
    ; finalMargin =
        Margin.wellFormedStepMargin step margin
    ; finalInterior =
        Margin.interiorFromUniqueMargin
          (WF.afterExactlyOneHead step)
          (Margin.wellFormedStepMargin step margin)
    }
  where
    interior =
      Margin.interiorFromUniqueMargin
        unique (weakenMarginToOne margin)

    step =
      Step.decodedAdjacentRowsFormMachineStep
        stateCoverage symbolCoverage nonempty
        (Transition.witness first) globalBits
        interior current
        (guards (Transition.witness first) interior current)

    after =
      Step.decodedAfterRow
        stateCoverage symbolCoverage
        (Transition.witness first) globalBits

buildDecodedRunNonempty
    stateCoverage symbolCoverage nonempty globalBits
    first (second ∷ rest)
    (Scan.semanticTimesStep current remaining)
    (orderedCons adjacent orderedRest)
    unique margin guards =
  record
    { rows = after ∷ rows recursive
    ; finish = finish recursive
    ; run =
        Run.runStep step
          (transportRunStart afterEq (run recursive))
    ; finalUnique = finalUnique recursive
    ; finalMargin = finalMargin recursive
    ; finalInterior = finalInterior recursive
    }
  where
    interior =
      Margin.interiorFromUniqueMargin
        unique (weakenMarginToOne margin)

    step =
      Step.decodedAdjacentRowsFormMachineStep
        stateCoverage symbolCoverage nonempty
        (Transition.witness first) globalBits
        interior current
        (guards (Transition.witness first) interior current)

    after =
      Step.decodedAfterRow
        stateCoverage symbolCoverage
        (Transition.witness first) globalBits

    afterEq =
      adjacentDecodedRows
        stateCoverage symbolCoverage adjacent globalBits

    afterUnique =
      WF.afterExactlyOneHead step

    afterMargin =
      Margin.wellFormedStepMargin step margin

    nextUnique =
      transportUniqueRow afterEq afterUnique

    nextMargin =
      transportMarginRow afterEq afterMargin

    recursive =
      buildDecodedRunNonempty
        stateCoverage symbolCoverage nonempty globalBits
        second rest remaining orderedRest
        nextUnique nextMargin guards

decodedAllSlotsRun :
  ∀ {machine cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps : Nat)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  (semantic :
    Scan.AllTimesSemantic {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty globalBits
      (Transition.allSlots steps)) →
  (startUnique :
    WF.ExactlyOneHead
      (Local.cells {machine}
        (Decode.decodeRow stateCoverage symbolCoverage cols
          (Global.rowSliceBits {machine} {steps} {cols}
            (Global.here {remaining = steps})
            globalBits)))) →
  (startMargin :
    Margin.HeadMargin (suc steps)
      (Local.cells {machine}
        (Decode.decodeRow stateCoverage symbolCoverage cols
          (Global.rowSliceBits {machine} {steps} {cols}
            (Global.here {remaining = steps})
            globalBits)))) →
  Step.AllTimeStepsBoundaryGuards {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits →
  DecodedRunResult {machine = machine}
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Global.here {remaining = steps})
        globalBits))
decodedAllSlotsRun
    {machine} {cols}
    stateCoverage symbolCoverage nonempty
    zero globalBits
    Scan.semanticTimesDone
    startUnique startMargin guards =
  record
    { rows = []
    ; finish = start
    ; run = Run.runDone
    ; finalUnique = startUnique
    ; finalMargin = startMargin
    ; finalInterior =
        Margin.interiorFromUniqueMargin {machine} startUnique startMargin
    }
  where
    start =
      Decode.decodeRow stateCoverage symbolCoverage cols
        (Global.rowSliceBits {machine} {zero} {cols}
          (Global.here {remaining = zero}) globalBits)

decodedAllSlotsRun
    {machine} {cols}
    stateCoverage symbolCoverage nonempty
    (suc steps) globalBits
    semantic
    startUnique startMargin guards =
  buildDecodedRunNonempty {machine} {suc steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits
    (Transition.some-slot zero (Global.here {remaining = steps}))
    (Transition.mapShiftSlots (Transition.allSlots steps))
    semantic
    (allSlotsOrdered (suc steps))
    startUnique
    (subst (λ len → Margin.HeadMargin len (Local.cells {machine} (Decode.decodeRow stateCoverage symbolCoverage cols (Global.rowSliceBits {machine} {suc steps} {cols} (Global.here {remaining = suc steps}) globalBits))))
           (cong suc (sym (allSlotsLength (suc steps))))
           startMargin)
    guards


------------------------------------------------------------------------
-- The run finish is the same final global row inspected by the endpoint CNF.
------------------------------------------------------------------------

data LastSlot {steps : Nat}
    (last : Transition.SomeSlot steps) :
    List (Transition.SomeSlot steps) → Set₁ where
  lastOne :
    LastSlot last (last ∷ [])
  lastCons :
    ∀ {head rest} →
    LastSlot last rest →
    LastSlot last (head ∷ rest)

shiftLastSlot :
  ∀ {steps}
    {last : Transition.SomeSlot steps}
    {times : List (Transition.SomeSlot steps)} →
  LastSlot last times →
  LastSlot
    (Transition.shiftSomeSlot last)
    (Transition.mapShiftSlots times)
shiftLastSlot lastOne =
  lastOne
shiftLastSlot (lastCons proof) =
  lastCons (shiftLastSlot proof)

lastTimeWitness :
  (n : Nat) →
  Global.Slot n (suc n)
lastTimeWitness zero =
  Global.here
lastTimeWitness (suc n) =
  Global.there (lastTimeWitness n)

lastTimeWitness_eq_finalRowSlot :
  (n : Nat) →
  lastTimeWitness n ≡ Endpoint.finalRowSlot n
lastTimeWitness_eq_finalRowSlot zero =
  refl
lastTimeWitness_eq_finalRowSlot (suc n)
  rewrite lastTimeWitness_eq_finalRowSlot n =
  refl

lastOfAllSlots :
  (n : Nat) →
  LastSlot
    (Transition.some-slot n (lastTimeWitness n))
    (Transition.allSlots (suc n))
lastOfAllSlots zero =
  lastOne
lastOfAllSlots (suc n) =
  lastCons
    (shiftLastSlot (lastOfAllSlots n))

buildDecodedRun_finish_eq_lastAfter :
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
    (ordered : OrderedSlotChain (first ∷ rest))
    (unique :
      WF.ExactlyOneHead
        (Local.cells
          (Step.decodedBeforeRow {machine} {steps} {cols} stateCoverage symbolCoverage
            (Transition.witness first) globalBits)))
    (margin :
      Margin.HeadMargin (suc (timesLength (first ∷ rest)))
        (Local.cells
          (Step.decodedBeforeRow {machine} {steps} {cols} stateCoverage symbolCoverage
            (Transition.witness first) globalBits)))
    (guards :
      Step.AllTimeStepsBoundaryGuards {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits)
    (last : Transition.SomeSlot steps) →
  LastSlot last (first ∷ rest) →
  DecodedRunResult.finish {machine = machine}
    (buildDecodedRunNonempty {machine} {steps} {cols}
      stateCoverage symbolCoverage nonempty globalBits
      first rest semantic ordered unique margin guards)
  ≡
  Step.decodedAfterRow {machine} {steps} {cols}
    stateCoverage symbolCoverage
    (Transition.witness last) globalBits
buildDecodedRun_finish_eq_lastAfter {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits
    (Transition.some-slot timeIndex timeSlot) []
    (Scan.semanticTimesStep current Scan.semanticTimesDone)
    orderedOne
    unique margin guards
    .(Transition.some-slot timeIndex timeSlot) lastOne =
  refl
buildDecodedRun_finish_eq_lastAfter {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits
    first (second ∷ rest)
    (Scan.semanticTimesStep current remaining)
    (orderedCons adjacent orderedRest)
    unique margin guards
    last (lastCons lastProof) =
  buildDecodedRun_finish_eq_lastAfter {machine} {steps} {cols}
    stateCoverage symbolCoverage nonempty globalBits
    second rest remaining orderedRest
    nextUnique nextMargin guards
    last lastProof
  where
    interior =
      Margin.interiorFromUniqueMargin
        unique (weakenMarginToOne margin)

    step =
      Step.decodedAdjacentRowsFormMachineStep {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty
        (Transition.witness first) globalBits
        interior current
        (guards (Transition.witness first) interior current)

    afterEq =
      adjacentDecodedRows {machine} {steps} {cols}
        stateCoverage symbolCoverage adjacent globalBits

    nextUnique =
      transportUniqueRow afterEq
        (WF.afterExactlyOneHead step)

    nextMargin =
      transportMarginRow afterEq
        (Margin.wellFormedStepMargin step margin)

lastAfterDecodedRow_eq_finalGlobalRow :
  ∀ {machine cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (n : Nat)
    (globalBits :
      CNF.Bits (Trace.GlobalTraceWidth machine (suc n) cols)) →
  Step.decodedAfterRow {machine} {suc n} {cols}
    stateCoverage symbolCoverage
    (lastTimeWitness n) globalBits
  ≡
  Decode.decodeRow stateCoverage symbolCoverage cols
    (Global.rowSliceBits {machine} {suc n} {cols}
      (Endpoint.finalRowSlot (suc n))
      globalBits)
lastAfterDecodedRow_eq_finalGlobalRow {machine} {cols}
    stateCoverage symbolCoverage n globalBits
    rewrite lastTimeWitness_eq_finalRowSlot n =
  refl

decodedAllSlotsRun_finish_eq_finalGlobalRow :
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
        (Local.cells
          (Decode.decodeRow stateCoverage symbolCoverage cols
            (Global.rowSliceBits {machine} {steps} {cols}
              (Global.here {remaining = steps})
              globalBits))))
    (startMargin :
      Margin.HeadMargin (suc steps)
        (Local.cells
          (Decode.decodeRow stateCoverage symbolCoverage cols
            (Global.rowSliceBits {machine} {steps} {cols}
              (Global.here {remaining = steps})
              globalBits))))
    (guards :
      Step.AllTimeStepsBoundaryGuards {machine} {steps} {cols}
        stateCoverage symbolCoverage nonempty globalBits) →
  DecodedRunResult.finish {machine = machine}
    (decodedAllSlotsRun {machine} {cols}
      stateCoverage symbolCoverage nonempty
      steps globalBits semantic startUnique startMargin guards)
  ≡
  Decode.decodeRow stateCoverage symbolCoverage cols
    (Global.rowSliceBits {machine} {steps} {cols}
      (Endpoint.finalRowSlot steps)
      globalBits)
decodedAllSlotsRun_finish_eq_finalGlobalRow
    {machine} {cols}
    stateCoverage symbolCoverage nonempty
    zero globalBits Scan.semanticTimesDone
    startUnique startMargin guards =
  refl
decodedAllSlotsRun_finish_eq_finalGlobalRow
    {machine} {cols}
    stateCoverage symbolCoverage nonempty
    (suc n) globalBits semantic startUnique startMargin guards =
  trans
    (buildDecodedRun_finish_eq_lastAfter {machine} {suc n} {cols}
      stateCoverage symbolCoverage nonempty globalBits
      (Transition.some-slot zero (Global.here {remaining = n}))
      (Transition.mapShiftSlots (Transition.allSlots n))
      semantic
      (allSlotsOrdered (suc n))
      startUnique
      (subst (λ len → Margin.HeadMargin len (Local.cells {machine} (Decode.decodeRow stateCoverage symbolCoverage cols (Global.rowSliceBits {machine} {suc n} {cols} (Global.here {remaining = suc n}) globalBits))))
             (cong suc (sym (allSlotsLength (suc n))))
             startMargin)
      guards
      (Transition.some-slot n (lastTimeWitness n))
      (lastOfAllSlots n))
    (lastAfterDecodedRow_eq_finalGlobalRow {machine} {cols}
      stateCoverage symbolCoverage n globalBits)

record DecodedRunInductionReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    allSlotsOrderedPaid : Bool
    adjacentRowsSameGlobalBlockPaid : Bool
    oneStepMarginThreadPaid : Bool
    allTimeSlicesToWellFormedRunPaid : Bool
    finalUniquePaid : Bool
    finalInteriorPaid : Bool

decodedRunInductionReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  DecodedRunInductionReceipt machine
decodedRunInductionReceipt machine = record
  { allSlotsOrderedPaid = true
  ; adjacentRowsSameGlobalBlockPaid = true
  ; oneStepMarginThreadPaid = true
  ; allTimeSlicesToWellFormedRunPaid = true
  ; finalUniquePaid = true
  ; finalInteriorPaid = true
  }
