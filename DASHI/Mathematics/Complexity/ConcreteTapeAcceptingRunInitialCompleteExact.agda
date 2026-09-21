module DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunInitialCompleteExact where

------------------------------------------------------------------------
-- REVERSE COOK--LEVIN: THE CONSTRUCTED RUN ASSIGNMENT SATISFIES ROW 0
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

takeBitsAll :
  ∀ {n} (bits : CNF.Bits n) →
  Canonical.takeBits n bits ≡ bits
takeBitsAll CNF.[]ᵇ = refl
takeBitsAll (bit CNF.∷ᵇ bits)
  rewrite takeBitsAll bits =
  refl

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
encodeRunRows_takeFirst
    stateCoverage symbolCoverage Run.runDone =
  takeBitsAll (Flat.encodeRow stateCoverage symbolCoverage _)
encodeRunRows_takeFirst
    stateCoverage symbolCoverage
    (Run.runStep step rest) =
  Canonical.takeAppendBits
    (Flat.encodeRow stateCoverage symbolCoverage _)
    _

encodeRunBaseTrace_rowsPrefix :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Slice.rowsPrefixBits
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
  ≡ Assignment.encodeRunRows
      stateCoverage symbolCoverage run
encodeRunBaseTrace_rowsPrefix
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
  Global.rowSliceBits
    (Global.here {remaining = Run.runLength run})
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
  ≡ Flat.encodeRow stateCoverage symbolCoverage start
encodedRunBase_rowZero
    stateCoverage symbolCoverage run =
  trans
    (Slice.rowSliceBits_eq_blockSlice
      Global.here
      (Assignment.encodeRunBaseTrace
        stateCoverage symbolCoverage run))
    (trans
      (cong
        (Canonical.takeBits
          (Canonical.listLength (Local.cells _) *
            Canonical.CellWidth _))
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
  FormulaSem.baseTraceBits
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡
  Assignment.encodeRunBaseTrace
    stateCoverage symbolCoverage
    (Accepting.run certificate)
encodedAcceptingAssignment_baseTrace
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
    (Endpoint.initialEndpointCNF
      (Flat.encodeRow stateCoverage symbolCoverage start))
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡ Agda.Builtin.Bool.true
encodedAcceptingAssignment_initialPullback
    stateCoverage symbolCoverage certificate =
  (Endpoint.initialEndpointCNF_iff
    (Flat.encodeRow stateCoverage symbolCoverage _)
    assignment).from initialExact
  where
    assignment =
      Assignment.encodeAcceptingRunAssignment
        stateCoverage symbolCoverage certificate

    run = Accepting.run certificate

    initialExact :
      DASHI.Mathematics.Complexity.CNFVariableRenamingExact.pullbackBits
        Endpoint.initialRowExtendedRename assignment
      ≡
      Flat.encodeRow stateCoverage symbolCoverage _
    initialExact =
      trans
        (sym
          (Sound.baseRowZeroBits_eq_endpointInitialBits
            (Accepting.acceptingRunLength certificate)
            (Canonical.listLength (Local.cells _))
            assignment))
        (trans
          (cong
            (Global.rowSliceBits
              (Global.here
                {remaining =
                  Accepting.acceptingRunLength certificate}))
            (encodedAcceptingAssignment_baseTrace
              stateCoverage symbolCoverage certificate))
          (encodedRunBase_rowZero
            stateCoverage symbolCoverage run))
