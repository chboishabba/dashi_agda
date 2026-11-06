module DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunInitialCompleteExact where

------------------------------------------------------------------------
-- REVERSE COOK--LEVIN: THE CONSTRUCTED RUN ASSIGNMENT SATISFIES ROW 0
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeInitialDecodeSameObjectExact as Initial
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

encodeRunRows_takeFirst :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Canonical.takeBits
    (Canonical.listLength (Local.cells start) *
      Canonical.CellWidth machine)
    (Assignment.encodeRunRows stateCoverage symbolCoverage run)
  ≡ Flat.encodeRow stateCoverage symbolCoverage start
encodeRunRows_takeFirst {machine} {start = start}
    stateCoverage symbolCoverage Run.runDone =
  Canonical.takeAppendBits
    (Flat.encodeRow {machine} stateCoverage symbolCoverage start)
    CNF.[]ᵇ
encodeRunRows_takeFirst {machine} {start = start}
    stateCoverage symbolCoverage
    (Run.runStep step rest) =
  Canonical.takeAppendBits
    (Flat.encodeRow {machine} stateCoverage symbolCoverage start)
    _

encodeRunBaseTrace_rowsPrefix :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Slice.rowsPrefixBits {machine}
    {Run.runLength run}
    {Canonical.listLength (Local.cells start)}
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
  ≡ Assignment.encodeRunRows
      stateCoverage symbolCoverage run
encodeRunBaseTrace_rowsPrefix {machine} {start = start}
    stateCoverage symbolCoverage run =
  Canonical.takeAppendBits
    (Assignment.encodeRunRows
      stateCoverage symbolCoverage run)
    (Assignment.encodeRunSelectors run)

encodedRunBase_rowZero :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Global.rowSliceBits {machine}
    {Run.runLength run}
    {Canonical.listLength (Local.cells start)}
    (Global.here {remaining = Run.runLength run})
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
  ≡ Flat.encodeRow stateCoverage symbolCoverage start
encodedRunBase_rowZero {machine} {start = start}
    stateCoverage symbolCoverage run =
  trans
    (Slice.rowSliceBits_eq_blockSlice {machine}
      {Run.runLength run}
      {Canonical.listLength (Local.cells start)}
      Global.here
      (Assignment.encodeRunBaseTrace
        stateCoverage symbolCoverage run))
    (trans
      (cong
        (Canonical.takeBits
          (Canonical.listLength (Local.cells start) *
            Canonical.CellWidth machine))
        (encodeRunBaseTrace_rowsPrefix
          stateCoverage symbolCoverage run))
      (encodeRunRows_takeFirst
        stateCoverage symbolCoverage run))

encodedAcceptingAssignment_baseTrace :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  FormulaSem.baseTraceBits {machine}
    {Accepting.acceptingRunLength certificate}
    {Canonical.listLength (Local.cells start)}
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡
  Assignment.encodeRunBaseTrace
    stateCoverage symbolCoverage
    (Accepting.run certificate)
encodedAcceptingAssignment_baseTrace {machine} {start = start}
    stateCoverage symbolCoverage certificate =
  trans
    (Slice.pullbackFinLeft_eq_takeBits
      (Assignment.encodeAcceptingRunAssignment
        stateCoverage symbolCoverage certificate))
    (Canonical.takeAppendBits
      (Assignment.encodeRunBaseTrace
        stateCoverage symbolCoverage
        (Accepting.run certificate))
      _)


decodedRunBase_finalRow :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Decode.decodeRow {machine = machine} stateCoverage symbolCoverage
    (Canonical.listLength (Local.cells start))
    (Global.rowSliceBits {machine}
      {Run.runLength run}
      {Canonical.listLength (Local.cells start)}
      (Endpoint.finalRowSlot (Run.runLength run))
      (Assignment.encodeRunBaseTrace
        stateCoverage symbolCoverage run))
  ≡ finish
decodedRunBase_finalRow {machine} {start = start}
    stateCoverage symbolCoverage run =
  trans
    (cong
      (λ s →
        Decode.decodeRow {machine = machine} stateCoverage symbolCoverage
          cols
          (Global.rowSliceBits {machine} {steps} {cols} s
            (Assignment.encodeRunBaseTrace stateCoverage symbolCoverage run)))
      (sym (Assignment.finalRunRowSlot_eq_finalRowSlot run)))
    (trans
      (cong
        (Decode.decodeRow {machine = machine} stateCoverage symbolCoverage cols)
        (trans
          (Slice.rowSliceBits_eq_blockSlice {machine} {steps} {cols}
            (Assignment.finalRunRowSlot run)
            (Assignment.encodeRunBaseTrace
              stateCoverage symbolCoverage run))
          (cong
            (Slice.blockSliceBits
              (Assignment.finalRunRowSlot run))
            (Assignment.encodeRunBaseTrace_rows
              stateCoverage symbolCoverage run))))
      (Assignment.encodeRunRows_finalBlock
        stateCoverage symbolCoverage run))
  where
    steps = Run.runLength run
    cols = Canonical.listLength (Local.cells start)

decodedAcceptingAssignment_finalRow :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  Decode.decodeRow {machine = machine} stateCoverage symbolCoverage
    (Canonical.listLength (Local.cells start))
    (Global.rowSliceBits {machine}
      {Accepting.acceptingRunLength certificate}
      {Canonical.listLength (Local.cells start)}
      (Endpoint.finalRowSlot
        (Accepting.acceptingRunLength certificate))
      (FormulaSem.baseTraceBits {machine}
        {Accepting.acceptingRunLength certificate}
        {Canonical.listLength (Local.cells start)}
        (Assignment.encodeAcceptingRunAssignment
          stateCoverage symbolCoverage certificate)))
  ≡ finish
decodedAcceptingAssignment_finalRow {machine} {start = start}
    stateCoverage symbolCoverage certificate =
  trans
    (cong
      (Decode.decodeRow {machine = machine} stateCoverage symbolCoverage
        (Canonical.listLength (Local.cells start)))
      (cong
        (Global.rowSliceBits {machine}
          {steps}
          {cols}
          (Endpoint.finalRowSlot steps))
        (encodedAcceptingAssignment_baseTrace
          stateCoverage symbolCoverage certificate)))
    (decodedRunBase_finalRow
      stateCoverage symbolCoverage
      (Accepting.run certificate))
  where
    steps = Accepting.acceptingRunLength certificate
    cols = Canonical.listLength (Local.cells start)

encodedAcceptingAssignment_initialPullback :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  CNF.evaluateCNF
    (Endpoint.initialEndpointCNF {machine}
      {Accepting.acceptingRunLength certificate}
      {Canonical.listLength (Local.cells start)}
      (Flat.encodeRow stateCoverage symbolCoverage start))
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡ true
encodedAcceptingAssignment_initialPullback {machine} {start = start}
    stateCoverage symbolCoverage certificate =
  Endpoint._↔_.from
    (Endpoint.initialEndpointCNF_iff {machine} {steps} {cols}
      (Flat.encodeRow {machine = machine} stateCoverage symbolCoverage start)
      assignment)
    initialExact
  where
    steps = Accepting.acceptingRunLength certificate
    cols = Canonical.listLength (Local.cells start)

    assignment =
      Assignment.encodeAcceptingRunAssignment
        stateCoverage symbolCoverage certificate

    run = Accepting.run certificate

    initialExact :
      Rename.pullbackBits
        (Endpoint.initialRowExtendedRename {machine} {steps} {cols})
        assignment
      ≡
      Flat.encodeRow {machine = machine} stateCoverage symbolCoverage start
    initialExact =
      trans
        (sym
          (Sound.baseRowZeroBits_eq_endpointInitialBits {machine}
            steps cols assignment))
        (trans
          (cong
            (Global.rowSliceBits {machine} {steps} {cols}
              (Global.here {remaining = steps}))
            (encodedAcceptingAssignment_baseTrace
              stateCoverage symbolCoverage certificate))
          (encodedRunBase_rowZero
            stateCoverage symbolCoverage run))
