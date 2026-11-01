module DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact where

------------------------------------------------------------------------
-- EXACT ACCEPTING RUN -> THE BOOLEAN VECTOR USED BY THE FINAL GLOBAL CNF
--
-- Layout:
--
--   [ canonical rows_0,...,rows_T ]
--   [ canonical shared rule selectors_0,...,selectors_{T-1} ]
--   [ one-hot accepting-head witness in the final row ]
--
-- No SAT satisfaction theorem is asserted here; this file pays the exact
-- representation half of the reverse Cook--Levin direction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Small equality transports
------------------------------------------------------------------------

castBits :
  ∀ {m n} →
  m ≡ n →
  CNF.Bits m →
  CNF.Bits n
castBits refl bits = bits

canonicalLength_eq_coordinateLength :
  ∀ {A : Set} (xs : List A) →
  Canonical.listLength xs ≡ Coordinate.listLength xs
canonicalLength_eq_coordinateLength [] = refl
canonicalLength_eq_coordinateLength (x ∷ xs)
  rewrite canonicalLength_eq_coordinateLength xs =
  refl

stepCanonicalLength :
  ∀ {machine before after} →
  WF.WellFormedMachineStep machine before after →
  Canonical.listLength (Local.cells before)
  ≡ Canonical.listLength (Local.cells after)
stepCanonicalLength step =
  trans
    (canonicalLength_eq_coordinateLength (Local.cells _))
    (trans
      (Whole.rewriteOccurrencePreservesLength
        (WF.occurrence (WF.wellFormedOccurrence step)))
      (sym
        (canonicalLength_eq_coordinateLength (Local.cells _))))

runFinishCanonicalLength :
  ∀ {machine start rows finish} →
  Run.WellFormedTapeRun machine start rows finish →
  Canonical.listLength (Local.cells start)
  ≡ Canonical.listLength (Local.cells finish)
runFinishCanonicalLength Run.runDone =
  refl
runFinishCanonicalLength (Run.runStep step rest) =
  trans
    (stepCanonicalLength step)
    (runFinishCanonicalLength rest)

------------------------------------------------------------------------
-- Canonical rows in exactly the repeated fixed-row layout
------------------------------------------------------------------------

encodeRunRows :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  CNF.Bits
    (Trace.RowsTraceWidth machine
      (Run.runLength run)
      (Canonical.listLength (Local.cells start)))
encodeRunRows stateCoverage symbolCoverage Run.runDone =
  Flat.encodeRow stateCoverage symbolCoverage _
encodeRunRows {machine} {start = current}
    stateCoverage symbolCoverage
    (Run.runStep {next = next} step rest) =
  Canonical.appendBits
    (Flat.encodeRow stateCoverage symbolCoverage _)
    tail
  where
    beforeCols =
      Canonical.listLength (Local.cells current)

    afterCols =
      Canonical.listLength (Local.cells next)

    tailRaw =
      encodeRunRows stateCoverage symbolCoverage rest

    tail :
      CNF.Bits
        (Trace.RowsTraceWidth machine
          (Run.runLength rest)
          beforeCols)
    tail =
      castBits
        (cong
          (Trace.RowsTraceWidth machine (Run.runLength rest))
          (sym (stepCanonicalLength step)))
        tailRaw


finalRunRowSlot :
  ∀ {machine start rows finish}
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Global.Slot (Run.runLength run) (suc (Run.runLength run))
finalRunRowSlot Run.runDone =
  Global.here
finalRunRowSlot (Run.runStep step rest) =
  Global.there (finalRunRowSlot rest)

encodeRunRows_finalBlock :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Slice.blockSliceBits
    (finalRunRowSlot run)
    (encodeRunRows stateCoverage symbolCoverage run)
  ≡ Flat.encodeRow stateCoverage symbolCoverage finish
encodeRunRows_finalBlock
    stateCoverage symbolCoverage Run.runDone =
  takeAll
    (Flat.encodeRow stateCoverage symbolCoverage _)
  where
    takeAll :
      ∀ {n} (bits : CNF.Bits n) →
      Canonical.takeBits n bits ≡ bits
    takeAll CNF.[]ᵇ = refl
    takeAll (bit CNF.∷ᵇ bits)
      rewrite takeAll bits =
      refl
encodeRunRows_finalBlock {machine} {start = current}
    stateCoverage symbolCoverage
    (Run.runStep {next = next} step rest)
    rewrite stepCanonicalLength step
          | Canonical.dropAppendBits
              (Flat.encodeRow stateCoverage symbolCoverage current)
              (encodeRunRows stateCoverage symbolCoverage rest) =
  encodeRunRows_finalBlock
    stateCoverage symbolCoverage rest


finalRunRowSlot_eq_finalRowSlot :
  ∀ {machine start rows finish}
    (run : Run.WellFormedTapeRun machine start rows finish) →
  finalRunRowSlot run ≡
    Endpoint.finalRowSlot (Run.runLength run)
finalRunRowSlot_eq_finalRowSlot Run.runDone =
  refl
finalRunRowSlot_eq_finalRowSlot
    (Run.runStep step rest)
    rewrite finalRunRowSlot_eq_finalRowSlot rest =
  refl

------------------------------------------------------------------------
-- One canonical shared selector per actual transition
------------------------------------------------------------------------

encodeRunSelectors :
  ∀ {machine start rows finish}
    (run : Run.WellFormedTapeRun machine start rows finish) →
  CNF.Bits
    (Trace.SelectorsTraceWidth machine (Run.runLength run))
encodeRunSelectors Run.runDone =
  CNF.[]ᵇ
encodeRunSelectors (Run.runStep step rest) =
  Canonical.appendBits
    (Selector.encodeRuleOccurs
      (Local.ruleOccursInMachine (WF.step step)))
    (encodeRunSelectors rest)

encodeRunBaseTrace :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  CNF.Bits
    (Trace.GlobalTraceWidth machine
      (Run.runLength run)
      (Canonical.listLength (Local.cells start)))
encodeRunBaseTrace stateCoverage symbolCoverage run =
  Canonical.appendBits
    (encodeRunRows stateCoverage symbolCoverage run)
    (encodeRunSelectors run)

------------------------------------------------------------------------
-- One-hot witness exactly at the accepting head
------------------------------------------------------------------------

oneHotAtOccurrence :
  ∀ {A : Set} {n : Nat} {x : A} {xs : List A} →
  Indexed.At n x xs →
  CNF.Bits (Canonical.listLength xs)
oneHotAtOccurrence {xs = x ∷ xs} Indexed.here =
  true CNF.∷ᵇ Selector.zeros (Canonical.listLength xs)
oneHotAtOccurrence {xs = y ∷ ys} (Indexed.there occurrence) =
  false CNF.∷ᵇ oneHotAtOccurrence occurrence

transportAtValue :
  ∀ {A : Set} {n : Nat} {x y : A} {xs : List A} →
  x ≡ y →
  Indexed.At n x xs →
  Indexed.At n y xs
transportAtValue refl occurrence =
  occurrence

headAtInterior :
  ∀ {machine row}
    (interior : Character.InteriorHeadConfiguration machine row) →
  Σ Nat (λ n →
    Indexed.At n
      (Local.headed
        (Character.headState interior)
        (Character.readSymbol interior))
      (Local.cells row))
headAtInterior interior
    with go
      (Character.prefix interior)
      (Character.prefixPlain interior)
... | n , occurrence =
  n ,
  transportAtList
    (sym (Character.rowShape interior))
    occurrence
  where
    transportAtList :
      ∀ {A : Set} {k : Nat} {x : A} {left right : List A} →
      left ≡ right →
      Indexed.At k x left →
      Indexed.At k x right
    transportAtList refl proof = proof

    go :
      ∀ prefix →
      WF.PlainCells prefix →
      Σ Nat (λ n →
        Indexed.At n
          (Local.headed
            (Character.headState interior)
            (Character.readSymbol interior))
          (Local.append prefix
            (Local.plain (Character.leftSymbol interior)
              ∷ Local.headed
                  (Character.headState interior)
                  (Character.readSymbol interior)
              ∷ Local.plain (Character.rightSymbol interior)
              ∷ Character.suffix interior)))
    go [] WF.plainNil =
      suc zero , Indexed.there Indexed.here
    go (Local.plain symbol ∷ prefix)
        (WF.plainCons plain)
        with go prefix plain
    ... | n , occurrence =
      suc n , Indexed.there occurrence

acceptingHeadOccurrence :
  ∀ {machine row} →
  Accepting.AcceptingInteriorRow machine row →
  Σ Nat (λ n →
    Σ (Local.Symbol machine) (λ symbol →
      Indexed.At n
        (Local.headed (Local.acceptingState machine) symbol)
        (Local.cells row)))
acceptingHeadOccurrence certificate
    with headAtInterior (Accepting.interior certificate)
... | n , occurrence =
  n ,
  Character.readSymbol (Accepting.interior certificate) ,
  transportAtValue
    (cong
      (λ q →
        Local.headed q
          (Character.readSymbol
            (Accepting.interior certificate)))
      (Accepting.headIsAccepting certificate))
    occurrence

acceptingWitnessBits :
  ∀ {machine row} →
  Accepting.AcceptingInteriorRow machine row →
  CNF.Bits (Canonical.listLength (Local.cells row))
acceptingWitnessBits certificate
    with acceptingHeadOccurrence certificate
... | n , symbol , occurrence =
  oneHotAtOccurrence occurrence

------------------------------------------------------------------------
-- Final exact global assignment
------------------------------------------------------------------------

encodeAcceptingRunAssignment :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  CNF.Bits
    (Endpoint.ExtendedGlobalWidth machine
      (Accepting.acceptingRunLength certificate)
      (Canonical.listLength (Local.cells start)))
encodeAcceptingRunAssignment
    stateCoverage symbolCoverage certificate =
  Canonical.appendBits
    (encodeRunBaseTrace
      stateCoverage symbolCoverage
      (Accepting.run certificate))
    witnessAtStartWidth
  where
    witnessAtFinishWidth =
      acceptingWitnessBits (Accepting.accepting certificate)

    witnessAtStartWidth :
      CNF.Bits (Canonical.listLength (Local.cells _))
    witnessAtStartWidth =
      castBits
        (sym
          (runFinishCanonicalLength
            (Accepting.run certificate)))
        witnessAtFinishWidth


------------------------------------------------------------------------
-- Exact projections of the final assignment
------------------------------------------------------------------------

encodeRunBaseTrace_rows :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Canonical.takeBits
    (Trace.RowsTraceWidth machine
      (Run.runLength run)
      (Canonical.listLength (Local.cells start)))
    (encodeRunBaseTrace stateCoverage symbolCoverage run)
  ≡ encodeRunRows stateCoverage symbolCoverage run
encodeRunBaseTrace_rows stateCoverage symbolCoverage run =
  Canonical.takeAppendBits
    (encodeRunRows stateCoverage symbolCoverage run)
    (encodeRunSelectors run)

encodeRunBaseTrace_selectors :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Canonical.dropBits
    (Trace.RowsTraceWidth machine
      (Run.runLength run)
      (Canonical.listLength (Local.cells start)))
    (encodeRunBaseTrace stateCoverage symbolCoverage run)
  ≡ encodeRunSelectors run
encodeRunBaseTrace_selectors stateCoverage symbolCoverage run =
  Canonical.dropAppendBits
    (encodeRunRows stateCoverage symbolCoverage run)
    (encodeRunSelectors run)

encodeAcceptingRunAssignment_base :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  Canonical.takeBits
    (Trace.GlobalTraceWidth machine
      (Accepting.acceptingRunLength certificate)
      (Canonical.listLength (Local.cells start)))
    (encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡ encodeRunBaseTrace
      stateCoverage symbolCoverage
      (Accepting.run certificate)
encodeAcceptingRunAssignment_base
    stateCoverage symbolCoverage certificate =
  Canonical.takeAppendBits
    (encodeRunBaseTrace
      stateCoverage symbolCoverage
      (Accepting.run certificate))
    _

encodeAcceptingRunAssignment_witness :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  Canonical.dropBits
    (Trace.GlobalTraceWidth machine
      (Accepting.acceptingRunLength certificate)
      (Canonical.listLength (Local.cells start)))
    (encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡
  castBits
    (sym (runFinishCanonicalLength
      (Accepting.run certificate)))
    (acceptingWitnessBits (Accepting.accepting certificate))
encodeAcceptingRunAssignment_witness
    stateCoverage symbolCoverage certificate =
  Canonical.dropAppendBits
    (encodeRunBaseTrace
      stateCoverage symbolCoverage
      (Accepting.run certificate))
    _

encodeRunSelectors_head :
  ∀ {machine current next tail finish}
    (step : WF.WellFormedMachineStep machine current next)
    (rest : Run.WellFormedTapeRun machine next tail finish) →
  Canonical.takeBits (Selector.RuleWidth machine)
    (encodeRunSelectors (Run.runStep step rest))
  ≡ Selector.encodeRuleOccurs
      (Local.ruleOccursInMachine (WF.step step))
encodeRunSelectors_head step rest =
  Canonical.takeAppendBits
    (Selector.encodeRuleOccurs
      (Local.ruleOccursInMachine (WF.step step)))
    (encodeRunSelectors rest)

encodeRunRows_head :
  ∀ {machine current next tail finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (step : WF.WellFormedMachineStep machine current next)
    (rest : Run.WellFormedTapeRun machine next tail finish) →
  Canonical.takeBits
    (Canonical.listLength (Local.cells current) *
      Canonical.CellWidth machine)
    (encodeRunRows stateCoverage symbolCoverage
      (Run.runStep step rest))
  ≡ Flat.encodeRow stateCoverage symbolCoverage current
encodeRunRows_head stateCoverage symbolCoverage step rest =
  Canonical.takeAppendBits
    (Flat.encodeRow stateCoverage symbolCoverage _)
    _

record AcceptingRunAssignmentReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    stepLengthPreservationPaid : Bool
    allCanonicalRowsPaid : Bool
    allCanonicalRuleSelectorsPaid : Bool
    finalAcceptingOneHotPaid : Bool
    exactGlobalLayoutPaid : Bool
    assignmentSatisfiesTransitionCNFPaid : Bool
    assignmentSatisfiesInitialCNFPaid : Bool
    assignmentSatisfiesAcceptingCNFPaid : Bool
    acceptingRunToSATPaid : Bool

acceptingRunAssignmentReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  AcceptingRunAssignmentReceipt machine
acceptingRunAssignmentReceipt machine = record
  { stepLengthPreservationPaid = true
  ; allCanonicalRowsPaid = true
  ; allCanonicalRuleSelectorsPaid = true
  ; finalAcceptingOneHotPaid = true
  ; exactGlobalLayoutPaid = true
  ; assignmentSatisfiesTransitionCNFPaid = false
  ; assignmentSatisfiesInitialCNFPaid = false
  ; assignmentSatisfiesAcceptingCNFPaid = false
  ; acceptingRunToSATPaid = false
  }
