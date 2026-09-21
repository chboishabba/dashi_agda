module DASHI.Mathematics.Complexity.ConcreteTapeEncodedRunSemanticScanExact where

------------------------------------------------------------------------
-- CANONICAL ENCODED RUN -> THE SAME SEMANTIC SCAN USED BY SAT SOUNDNESS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeArbitrarySelectedWindowSemanticExact as Semantic
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedWholeRowSemanticExact as WholeDecoded
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedWindowSameObjectExact as Same
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapePlacedWholeRowCNFExact as IndexedScan
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunDecodeExact as RunDecode
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Slot occurrences in generic fixed-block decoders
------------------------------------------------------------------------

decodeRowsAtSlot :
  ∀ {machine index count}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (cols : Nat)
    (slot : Global.Slot index count)
    (bits : CNF.Bits (count * Decode.RowBitsWidth machine cols)) →
  Indexed.At index
    (Decode.decodeRow stateCoverage symbolCoverage cols
      (Slice.blockSliceBits slot bits))
    (Decode.decodeRows
      stateCoverage symbolCoverage count cols bits)
decodeRowsAtSlot stateCoverage symbolCoverage cols
    Global.here bits =
  Indexed.here
decodeRowsAtSlot {machine}
    stateCoverage symbolCoverage cols
    (Global.there slot) bits =
  Indexed.there
    (decodeRowsAtSlot
      stateCoverage symbolCoverage cols slot
      (Canonical.dropBits
        (Decode.RowBitsWidth machine cols) bits))

decodeSelectorsAtSlot :
  ∀ {machine index count}
    (nonempty : Selector.NonemptyRuleTable machine)
    (slot : Global.Slot index count)
    (bits : CNF.Bits (Trace.SelectorsTraceWidth machine count)) →
  Indexed.At index
    (Selector.decodeRuleChoice nonempty
      (Slice.blockSliceBits slot bits))
    (Trace.decodeSelectors nonempty count bits)
decodeSelectorsAtSlot nonempty Global.here bits =
  Indexed.here
decodeSelectorsAtSlot {machine} nonempty
    (Global.there slot) bits =
  Indexed.there
    (decodeSelectorsAtSlot
      nonempty slot
      (Canonical.dropBits
        (Selector.RuleWidth machine) bits))

transportAtList :
  ∀ {A : Set} {n : Nat} {x : A}
    {left right : List A} →
  left ≡ right →
  Indexed.At n x left →
  Indexed.At n x right
transportAtList refl occurrence = occurrence

atValueUnique :
  ∀ {A : Set} {n : Nat} {x y : A} {xs : List A} →
  Indexed.At n x xs →
  Indexed.At n y xs →
  x ≡ y
atValueUnique Indexed.here Indexed.here =
  refl
atValueUnique
    (Indexed.there left)
    (Indexed.there right) =
  atValueUnique left right

------------------------------------------------------------------------
-- The literal run step at any transition slot
------------------------------------------------------------------------

record RunStepAt
    {machine : Local.ConcreteTapeMachine}
    {start rows finish}
    (run : Run.WellFormedTapeRun machine start rows finish)
    {index : Nat}
    (slot : Global.Slot index (Run.runLength run)) : Set₁ where
  field
    before after : Local.TapeRow machine
    step : WF.WellFormedMachineStep machine before after

    beforeAt :
      Indexed.At index before (RunDecode.runRows run)

    afterAt :
      Indexed.At (suc index) after (RunDecode.runRows run)

    ruleAt :
      Indexed.At index
        (Selector.listed-rule
          (Local.rule (WF.step step))
          (Local.ruleOccursInMachine (WF.step step)))
        (RunDecode.runRuleChoices run)

open RunStepAt public

runStepAt :
  ∀ {machine start rows finish index}
    (run : Run.WellFormedTapeRun machine start rows finish)
    (slot : Global.Slot index (Run.runLength run)) →
  RunStepAt run slot
runStepAt Run.runDone ()
runStepAt
    (Run.runStep {current = current} {next = next}
      step rest)
    Global.here =
  record
    { before = current
    ; after = next
    ; step = step
    ; beforeAt = Indexed.here
    ; afterAt = Indexed.there Indexed.here
    ; ruleAt = Indexed.here
    }
runStepAt
    (Run.runStep step rest)
    (Global.there slot)
    with runStepAt rest slot
... | projection =
  record
    { before = before projection
    ; after = after projection
    ; step = step projection
    ; beforeAt = Indexed.there (beforeAt projection)
    ; afterAt = Indexed.there (afterAt projection)
    ; ruleAt = Indexed.there (ruleAt projection)
    }

------------------------------------------------------------------------
-- Canonical base-trace slices decode to that exact literal step
------------------------------------------------------------------------

record EncodedRunStepProjection
    {machine : Local.ConcreteTapeMachine}
    {start rows finish index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (run : Run.WellFormedTapeRun machine start rows finish)
    (slot : Global.Slot index (Run.runLength run)) : Set₁ where
  field
    literal : RunStepAt run slot

    decodedBefore :
      Decode.decodeRow stateCoverage symbolCoverage
        (Canonical.listLength (Local.cells start))
        (Global.rowSliceBits
          (Global.sameSlotInSucc slot)
          (Assignment.encodeRunBaseTrace
            stateCoverage symbolCoverage run))
      ≡ before literal

    decodedAfter :
      Decode.decodeRow stateCoverage symbolCoverage
        (Canonical.listLength (Local.cells start))
        (Global.rowSliceBits
          (Global.nextSlotInSucc slot)
          (Assignment.encodeRunBaseTrace
            stateCoverage symbolCoverage run))
      ≡ after literal

    decodedRule :
      WholeDecoded.ruleAtTime nonempty slot
        (Assignment.encodeRunBaseTrace
          stateCoverage symbolCoverage run)
      ≡ Local.rule (WF.step (step literal))

open EncodedRunStepProjection public

encodedRunStepProjection :
  ∀ {machine start rows finish index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (run : Run.WellFormedTapeRun machine start rows finish)
    (slot : Global.Slot index (Run.runLength run)) →
  EncodedRunStepProjection
    stateCoverage symbolCoverage nonempty run slot
encodedRunStepProjection
    {machine} {start = start}
    stateCoverage symbolCoverage nonempty run slot =
  record
    { literal = literalStep
    ; decodedBefore = decodedBeforeEq
    ; decodedAfter = decodedAfterEq
    ; decodedRule = decodedRuleEq
    }
  where
    cols = Canonical.listLength (Local.cells start)
    base = Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run
    rowsBits = Slice.rowsPrefixBits base
    selectorsBits = Slice.selectorsSuffixBits base

    literalStep = runStepAt run slot

    rowsDecodedEq :
      Decode.decodeRows
        stateCoverage symbolCoverage
        (suc (Run.runLength run)) cols rowsBits
      ≡ RunDecode.runRows run
    rowsDecodedEq
      rewrite Assignment.encodeRunBaseTrace_rows
        stateCoverage symbolCoverage run =
      RunDecode.decodeRunRows_encodeRunRows
        stateCoverage symbolCoverage run

    beforeOccurrence :
      Indexed.At _
        (Decode.decodeRow stateCoverage symbolCoverage cols
          (Global.rowSliceBits
            (Global.sameSlotInSucc slot) base))
        (RunDecode.runRows run)
    beforeOccurrence =
      transportAtList rowsDecodedEq
        (transportValue
          (cong
            (Decode.decodeRow stateCoverage symbolCoverage cols)
            (Slice.rowSliceBits_eq_blockSlice
              (Global.sameSlotInSucc slot) base))
          (decodeRowsAtSlot
            stateCoverage symbolCoverage cols
            (Global.sameSlotInSucc slot) rowsBits))
      where
        transportValue :
          ∀ {A : Set} {n : Nat} {x y : A} {xs : List A} →
          x ≡ y →
          Indexed.At n y xs →
          Indexed.At n x xs
        transportValue refl occurrence = occurrence

    afterOccurrence :
      Indexed.At _
        (Decode.decodeRow stateCoverage symbolCoverage cols
          (Global.rowSliceBits
            (Global.nextSlotInSucc slot) base))
        (RunDecode.runRows run)
    afterOccurrence =
      transportAtList rowsDecodedEq
        (transportValue
          (cong
            (Decode.decodeRow stateCoverage symbolCoverage cols)
            (Slice.rowSliceBits_eq_blockSlice
              (Global.nextSlotInSucc slot) base))
          (decodeRowsAtSlot
            stateCoverage symbolCoverage cols
            (Global.nextSlotInSucc slot) rowsBits))
      where
        transportValue :
          ∀ {A : Set} {n : Nat} {x y : A} {xs : List A} →
          x ≡ y →
          Indexed.At n y xs →
          Indexed.At n x xs
        transportValue refl occurrence = occurrence

    decodedBeforeEq =
      atValueUnique
        beforeOccurrence
        (beforeAt literalStep)

    decodedAfterEq =
      atValueUnique
        afterOccurrence
        (afterAt literalStep)

    selectorsDecodedEq :
      Trace.decodeSelectors nonempty
        (Run.runLength run) selectorsBits
      ≡ RunDecode.runRuleChoices run
    selectorsDecodedEq
      rewrite Assignment.encodeRunBaseTrace_selectors
        stateCoverage symbolCoverage run =
      RunDecode.decodeRunSelectors_encodeRunSelectors
        nonempty run

    decodedChoiceOccurrence :
      Indexed.At _
        (Selector.decodeRuleChoice nonempty
          (Global.selectorSliceBits slot base))
        (RunDecode.runRuleChoices run)
    decodedChoiceOccurrence =
      transportAtList selectorsDecodedEq
        (transportValue
          (cong
            (Selector.decodeRuleChoice nonempty)
            (Slice.selectorSliceBits_eq_blockSlice slot base))
          (decodeSelectorsAtSlot
            nonempty slot selectorsBits))
      where
        transportValue :
          ∀ {A : Set} {n : Nat} {x y : A} {xs : List A} →
          x ≡ y →
          Indexed.At n y xs →
          Indexed.At n x xs
        transportValue refl occurrence = occurrence

    choiceEq :
      Selector.decodeRuleChoice nonempty
        (Global.selectorSliceBits slot base)
      ≡ Selector.listed-rule
          (Local.rule (WF.step (step literalStep)))
          (Local.ruleOccursInMachine
            (WF.step (step literalStep)))
    choiceEq =
      atValueUnique
        decodedChoiceOccurrence
        (ruleAt literalStep)

    decodedRuleEq =
      cong Selector.selectedRule choiceEq

------------------------------------------------------------------------
-- Convert Whole.AllWindowsLegal back to native indexed legality
------------------------------------------------------------------------

allWindowsLegalToAllIndexedLegal :
  ∀ {machine rule before after} →
  Whole.AllWindowsLegal machine rule before after →
  IndexedScan.AllIndexedLegal rule
    (IndexedScan.scanIndexedWindows machine before after)
allWindowsLegalToAllIndexedLegal
    {machine} {rule} {before} {after} legal
    with IndexedScan.scanIndexed_forget machine before after
... | refl =
  go legal
  where
    go :
      ∀ {occurrences} →
      Whole.All
        (Pattern.LegalWindowForRule machine rule)
        (IndexedScan.mapForgetIndexed occurrences) →
      IndexedScan.AllIndexedLegal rule occurrences
    go Whole.allNil =
      IndexedScan.allIndexedNil
    go (Whole.allCons current rest) =
      IndexedScan.allIndexedCons current (go rest)

------------------------------------------------------------------------
-- Native indexed legality -> raw semantic witnesses at the same starts
------------------------------------------------------------------------

indexedLegalToRawSemantic :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  IndexedScan.AllIndexedLegal
    (WholeDecoded.ruleAtTime nonempty timeSlot globalBits)
    (WholeDecoded.decodedWindowsForStarts
      stateCoverage symbolCoverage timeSlot starts globalBits) →
  Scan.AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits starts
indexedLegalToRawSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot [] globalBits IndexedScan.allIndexedNil =
  Scan.semanticWindowsDone
indexedLegalToRawSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot
    (Transition.some-window-start index start ∷ rest)
    globalBits
    (IndexedScan.allIndexedCons current remaining) =
  Scan.semanticWindowsStep
    semantic
    (indexedLegalToRawSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot rest globalBits remaining)
  where
    rawBits = Raw.rawSelectedWindowBits timeSlot start globalBits

    semantic :
      Semantic.RawDecodedWindowSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot start globalBits
    semantic = record
      { Semantic.rule =
          WholeDecoded.ruleAtTime nonempty timeSlot globalBits
      ; Semantic.window =
          Indexed.forgetIndex
            (Same.decodedAdjacentWindow
              stateCoverage symbolCoverage timeSlot start globalBits)
      ; Semantic.ruleExact =
          sym
            (WholeDecoded.semanticRule_eq_ruleAtTime
              fakeSemantic)
      ; Semantic.windowExact =
          sym
            (Same.decodedRawWindowEqualsAdjacentRowsWindow
              stateCoverage symbolCoverage nonempty
              timeSlot start globalBits)
      ; Semantic.legal = current
      }
      where
        fakeSemantic :
          Semantic.RawDecodedWindowSemantic
            stateCoverage symbolCoverage nonempty
            timeSlot start globalBits
        fakeSemantic = record
          { Semantic.rule =
              Semantic.decodedSelectedRule nonempty rawBits
          ; Semantic.window =
              Semantic.decodedSelectedWindow
                stateCoverage symbolCoverage rawBits
          ; Semantic.ruleExact = refl
          ; Semantic.windowExact = refl
          ; Semantic.legal =
              transportLegal current
          }

        transportLegal :
          Pattern.LegalWindowForRule machine
            (WholeDecoded.ruleAtTime nonempty timeSlot globalBits)
            (Indexed.forgetIndex
              (Same.decodedAdjacentWindow
                stateCoverage symbolCoverage timeSlot start globalBits)) →
          Pattern.LegalWindowForRule machine
            (Semantic.decodedSelectedRule nonempty rawBits)
            (Semantic.decodedSelectedWindow
              stateCoverage symbolCoverage rawBits)
        transportLegal legal
          rewrite WholeDecoded.rawRuleEq
                | Same.decodedRawWindowEqualsAdjacentRowsWindow
                    stateCoverage symbolCoverage nonempty
                    timeSlot start globalBits =
          legal

------------------------------------------------------------------------
-- One encoded run step yields the semantic raw scan at that slot
------------------------------------------------------------------------

encodedRunSlotSemantic :
  ∀ {machine start rows finish index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (run : Run.WellFormedTapeRun machine start rows finish)
    (slot : Global.Slot index (Run.runLength run)) →
  Scan.AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    slot
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
    (Transition.allWindowStarts
      (Canonical.listLength (Local.cells start)))
encodedRunSlotSemantic
    stateCoverage symbolCoverage nonempty run slot =
  indexedLegalToRawSemantic
    stateCoverage symbolCoverage nonempty slot
    (Transition.allWindowStarts cols)
    base
    transported
  where
    cols = Canonical.listLength (Local.cells _)
    base = Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run
    projection =
      encodedRunStepProjection
        stateCoverage symbolCoverage nonempty run slot
    literalStep = literal projection

    actualLegal :
      Whole.AllWindowsLegal machine
        (Local.rule (WF.step (step literalStep)))
        (before literalStep)
        (after literalStep)
    actualLegal =
      Character.everyWindowLegal
        (Character.wellFormedStepGivesLocalityScan
          (step literalStep))

    actualIndexed =
      allWindowsLegalToAllIndexedLegal actualLegal

    scanEq =
      WholeDecoded.decodedAllStarts_eq_indexedScan
        stateCoverage symbolCoverage slot base

    transported :
      IndexedScan.AllIndexedLegal
        (WholeDecoded.ruleAtTime nonempty slot base)
        (WholeDecoded.decodedWindowsForStarts
          stateCoverage symbolCoverage slot
          (Transition.allWindowStarts cols) base)
    transported
      rewrite scanEq
            | decodedBefore projection
            | decodedAfter projection
            | decodedRule projection =
      actualIndexed

------------------------------------------------------------------------
-- Every slot in the canonical run encoding
------------------------------------------------------------------------

encodedRunTimesSemantic :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (run : Run.WellFormedTapeRun machine start rows finish)
    (times : List (Transition.SomeSlot (Run.runLength run))) →
  Scan.AllTimesSemantic
    stateCoverage symbolCoverage nonempty
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
    times
encodedRunTimesSemantic
    stateCoverage symbolCoverage nonempty run [] =
  Scan.semanticTimesDone
encodedRunTimesSemantic
    stateCoverage symbolCoverage nonempty run
    (Transition.some-slot index slot ∷ rest) =
  Scan.semanticTimesStep
    (encodedRunSlotSemantic
      stateCoverage symbolCoverage nonempty run slot)
    (encodedRunTimesSemantic
      stateCoverage symbolCoverage nonempty run rest)

encodedRunSemanticScan :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Scan.AllTimesSemantic
    stateCoverage symbolCoverage nonempty
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
    (Transition.allSlots (Run.runLength run))
encodedRunSemanticScan
    stateCoverage symbolCoverage nonempty run =
  encodedRunTimesSemantic
    stateCoverage symbolCoverage nonempty run
    (Transition.allSlots (Run.runLength run))
