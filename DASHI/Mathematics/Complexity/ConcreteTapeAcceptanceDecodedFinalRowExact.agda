module DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceDecodedFinalRowExact where

------------------------------------------------------------------------
-- ACCEPTANCE WITNESS CELL = AN ACTUAL CELL OF THE DECODED FINAL ROW
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedWindowSameObjectExact as Same
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceEndpointSoundExact as Accept
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

baseTraceBits :
  ∀ {machine steps cols} →
  CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols) →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols)
baseTraceBits {machine} {steps} {cols} assignment =
  Rename.pullbackBits (Endpoint.liftBaseIndex {machine} {steps} {cols}) assignment

extendedFinalCellBits :
  ∀ {machine steps cols}
    (i : Fin.Fin cols)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  CNF.Bits (Canonical.CellWidth machine)
extendedFinalCellBits {machine} {steps} {cols} i assignment =
  Rename.pullbackBits
    (λ j →
      Endpoint.liftBaseIndex {machine} {steps} {cols}
        (Global.globalRowRename {machine} {steps} {cols}
          (Endpoint.finalRowSlot steps)
          (Global.blockRename (Endpoint.finToSlot i) j)))
    assignment

extendedFinalCellBits_eq_baseCellPullback :
  ∀ {machine steps cols}
    (i : Fin.Fin cols)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  extendedFinalCellBits {machine} {steps} {cols} i assignment
  ≡
  Rename.pullbackBits
    (Raw.globalCellRename {machine} {steps} {cols}
      (Endpoint.finalRowSlot steps)
      (Endpoint.finToSlot i))
    (baseTraceBits {machine} {steps} {cols} assignment)
extendedFinalCellBits_eq_baseCellPullback {machine} {steps} {cols} i assignment =
  Same.pullbackCompose
    (Raw.globalCellRename {machine} {steps} {cols}
      (Endpoint.finalRowSlot steps)
      (Endpoint.finToSlot i))
    (Endpoint.liftBaseIndex {machine} {steps} {cols})
    assignment

-- The direct lookup proof avoids depending on the presentation chosen above.
extendedFinalCellBits_eq_finalRowBlock :
  ∀ {machine steps cols}
    (i : Fin.Fin cols)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  extendedFinalCellBits {machine} {steps} {cols} i assignment
  ≡
  Slice.blockSliceBits {width = Canonical.CellWidth machine} (Endpoint.finToSlot i)
    (Global.rowSliceBits {machine} {steps} {cols}
      (Endpoint.finalRowSlot steps)
      (baseTraceBits {machine} {steps} {cols} assignment))
extendedFinalCellBits_eq_finalRowBlock {machine} {steps} {cols} i assignment =
  trans
    (extendedFinalCellBits_eq_baseCellPullback {machine} {steps} {cols} i assignment)
    (Same.globalCellBits_eq_rowBlockSlice {machine} {steps} {cols}
      (Endpoint.finalRowSlot steps)
      (Endpoint.finToSlot i)
      (baseTraceBits {machine} {steps} {cols} assignment))

record AcceptingCellInDecodedFinalRow
    {machine : Local.ConcreteTapeMachine}
    {steps cols : Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) : Set where
  field
    index : Fin.Fin cols
    symbol : Local.Symbol machine
    occurs :
      Indexed.At (Fin.toℕ index)
        (Local.headed (Local.acceptingState machine) symbol)
        (Local.cells {machine}
          (Decode.decodeRow {machine} stateCoverage symbolCoverage cols
            (Global.rowSliceBits {machine} {steps} {cols}
              (Endpoint.finalRowSlot steps)
              (baseTraceBits {machine} {steps} {cols} assignment))))

open AcceptingCellInDecodedFinalRow public

acceptanceWitnessCellIsDecodedFinalCell :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  Accept.DecodedAcceptingCell {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment →
  AcceptingCellInDecodedFinalRow {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
acceptanceWitnessCellIsDecodedFinalCell
    {machine = machine} {steps = steps} {cols = cols}
    stateCoverage symbolCoverage assignment witness =
  record
    { index = Accept.index witness
    ; symbol = Accept.decodedSymbol witness
    ; occurs =
        transportAt decodedEq rawOccurrence
    }
  where
    i = Accept.index witness
    cellSlot = Endpoint.finToSlot i

    rawOccurrence :
      Indexed.At (Fin.toℕ i)
        (Canonical.decodeCell {machine} stateCoverage symbolCoverage
          (Slice.blockSliceBits {width = Canonical.CellWidth machine} cellSlot
            (Global.rowSliceBits {machine} {steps} {cols}
              (Endpoint.finalRowSlot steps)
              (baseTraceBits {machine} {steps} {cols} assignment))))
        (Local.cells {machine}
          (Decode.decodeRow {machine} stateCoverage symbolCoverage cols
            (Global.rowSliceBits {machine} {steps} {cols}
              (Endpoint.finalRowSlot steps)
              (baseTraceBits {machine} {steps} {cols} assignment))))
    rawOccurrence =
      Same.decodeCellsAtBlockSlice {machine} {count = cols}
        stateCoverage symbolCoverage cellSlot
        (Global.rowSliceBits {machine} {steps} {cols}
          (Endpoint.finalRowSlot steps)
          (baseTraceBits {machine} {steps} {cols} assignment))

    decodedEq :
      Canonical.decodeCell {machine} stateCoverage symbolCoverage
        (Slice.blockSliceBits {width = Canonical.CellWidth machine} cellSlot
          (Global.rowSliceBits {machine} {steps} {cols}
            (Endpoint.finalRowSlot steps)
            (baseTraceBits {machine} {steps} {cols} assignment)))
      ≡
      Local.headed (Local.acceptingState machine)
        (Accept.decodedSymbol witness)
    decodedEq =
      trans
        (cong
          (Canonical.decodeCell {machine} stateCoverage symbolCoverage)
          (sym (extendedFinalCellBits_eq_finalRowBlock {machine} {steps} {cols}
            i assignment)))
        (trans
          (cong
            (Canonical.decodeCell {machine} stateCoverage symbolCoverage)
            (sym (Accept.cellBitsExact witness)))
          (Accept.decodedAccepting witness))

    transportAt :
      ∀ {A : Set} {n} {x y : A} {xs} →
      x ≡ y →
      Indexed.At n x xs →
      Indexed.At n y xs
    transportAt refl proof = proof

record AcceptanceDecodedFinalRowReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    acceptanceExtendedCellEqualsBaseCellPaid : Bool
    acceptanceCellEqualsFinalDecodedRowBlockPaid : Bool
    acceptingWitnessOccursInDecodedFinalRowPaid : Bool

acceptanceDecodedFinalRowReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  AcceptanceDecodedFinalRowReceipt machine
acceptanceDecodedFinalRowReceipt machine = record
  { acceptanceExtendedCellEqualsBaseCellPaid = true
  ; acceptanceCellEqualsFinalDecodedRowBlockPaid = true
  ; acceptingWitnessOccursInDecodedFinalRowPaid = true
  }
