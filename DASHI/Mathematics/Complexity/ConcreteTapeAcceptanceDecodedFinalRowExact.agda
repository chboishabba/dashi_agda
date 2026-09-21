module DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceDecodedFinalRowExact where

------------------------------------------------------------------------
-- ACCEPTANCE WITNESS CELL = AN ACTUAL CELL OF THE DECODED FINAL ROW
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
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
baseTraceBits assignment =
  Rename.pullbackBits Endpoint.liftBaseIndex assignment

extendedFinalCellBits :
  ∀ {machine steps cols}
    (i : Fin.Fin cols)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  CNF.Bits (Canonical.CellWidth machine)
extendedFinalCellBits i assignment =
  Rename.pullbackBits
    (λ j →
      Endpoint.liftBaseIndex
        (Global.globalRowRename
          (Endpoint.finalRowSlot _)
          (Global.blockRename (Endpoint.finToSlot i) j)))
    assignment

extendedFinalCellBits_eq_baseCellPullback :
  ∀ {machine steps cols}
    (i : Fin.Fin cols)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  extendedFinalCellBits i assignment
  ≡
  Rename.pullbackBits
    (Global.globalCellRename
      (Endpoint.finalRowSlot steps)
      (Endpoint.finToSlot i))
    (baseTraceBits assignment)
extendedFinalCellBits_eq_baseCellPullback
    {steps = steps} i assignment =
  Same.pullbackCompose
    (Global.blockRename (Endpoint.finToSlot i))
    (Global.globalRowRename (Endpoint.finalRowSlot steps))
    (baseTraceBits assignment)
  |> trans extendedToBase
  where
    _|>_ : ∀ {A B : Set} → A → (A → B) → B
    x |> f = f x

    extendedToBase :
      Rename.pullbackBits
        (λ j →
          Global.globalRowRename
            (Endpoint.finalRowSlot steps)
            (Global.blockRename (Endpoint.finToSlot i) j))
        (baseTraceBits assignment)
      ≡ extendedFinalCellBits i assignment →
      extendedFinalCellBits i assignment
      ≡
      Rename.pullbackBits
        (Global.globalCellRename
          (Endpoint.finalRowSlot steps)
          (Endpoint.finToSlot i))
        (baseTraceBits assignment)
    extendedToBase _ =
      sym
        (Same.pullbackCompose
          (λ j →
            Global.globalRowRename
              (Endpoint.finalRowSlot steps)
              (Global.blockRename (Endpoint.finToSlot i) j))
          Endpoint.liftBaseIndex assignment)

-- The direct lookup proof avoids depending on the presentation chosen above.
extendedFinalCellBits_eq_finalRowBlock :
  ∀ {machine steps cols}
    (i : Fin.Fin cols)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  extendedFinalCellBits i assignment
  ≡
  Slice.blockSliceBits (Endpoint.finToSlot i)
    (Global.rowSliceBits
      (Endpoint.finalRowSlot steps)
      (baseTraceBits assignment))
extendedFinalCellBits_eq_finalRowBlock
    {steps = steps} i assignment =
  trans
    baseEq
    (Same.globalCellBits_eq_rowBlockSlice
      (Endpoint.finalRowSlot steps)
      (Endpoint.finToSlot i)
      (baseTraceBits assignment))
  where
    baseEq :
      extendedFinalCellBits i assignment
      ≡
      Rename.pullbackBits
        (Raw.globalCellRename
          (Endpoint.finalRowSlot steps)
          (Endpoint.finToSlot i))
        (baseTraceBits assignment)
    baseEq =
      Same.pullbackCompose
        (Global.blockRename (Endpoint.finToSlot i))
        (Global.globalRowRename (Endpoint.finalRowSlot steps))
        (baseTraceBits assignment)
      |> λ hbase →
        trans
          (sym
            (Same.pullbackCompose
              (λ j →
                Global.globalRowRename
                  (Endpoint.finalRowSlot steps)
                  (Global.blockRename (Endpoint.finToSlot i) j))
              Endpoint.liftBaseIndex assignment))
          hbase
    _|>_ : ∀ {A B : Set} → A → (A → B) → B
    x |> f = f x

record AcceptingCellInDecodedFinalRow
    {machine : Local.ConcreteTapeMachine}
    {steps cols : Agda.Builtin.Nat.Nat}
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
        (Local.cells
          (Decode.decodeRow stateCoverage symbolCoverage cols
            (Global.rowSliceBits
              (Endpoint.finalRowSlot steps)
              (baseTraceBits assignment))))

open AcceptingCellInDecodedFinalRow public

acceptanceWitnessCellIsDecodedFinalCell :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  Accept.DecodedAcceptingCell
    stateCoverage symbolCoverage assignment →
  AcceptingCellInDecodedFinalRow
    stateCoverage symbolCoverage assignment
acceptanceWitnessCellIsDecodedFinalCell
    {steps = steps} stateCoverage symbolCoverage
    assignment witness =
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
        (Canonical.decodeCell stateCoverage symbolCoverage
          (Slice.blockSliceBits cellSlot
            (Global.rowSliceBits
              (Endpoint.finalRowSlot steps)
              (baseTraceBits assignment))))
        (Local.cells
          (Decode.decodeRow stateCoverage symbolCoverage _
            (Global.rowSliceBits
              (Endpoint.finalRowSlot steps)
              (baseTraceBits assignment))))
    rawOccurrence =
      Same.decodeCellsAtBlockSlice
        stateCoverage symbolCoverage cellSlot
        (Global.rowSliceBits
          (Endpoint.finalRowSlot steps)
          (baseTraceBits assignment))

    decodedEq :
      Canonical.decodeCell stateCoverage symbolCoverage
        (Slice.blockSliceBits cellSlot
          (Global.rowSliceBits
            (Endpoint.finalRowSlot steps)
            (baseTraceBits assignment)))
      ≡
      Local.headed (Local.acceptingState machine)
        (Accept.decodedSymbol witness)
    decodedEq =
      trans
        (cong
          (Canonical.decodeCell stateCoverage symbolCoverage)
          (sym (extendedFinalCellBits_eq_finalRowBlock
            i assignment)))
        (trans
          (cong
            (Canonical.decodeCell stateCoverage symbolCoverage)
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
