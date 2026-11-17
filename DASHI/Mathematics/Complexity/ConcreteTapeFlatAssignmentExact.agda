module DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact where

------------------------------------------------------------------------
-- CONCRETE TAPE ROWS / FINITE RUNS -> ONE FLAT BOOLEAN ASSIGNMENT
--
-- This instantiates the generic finite-tableau representation on the actual
-- concrete tape carrier.  Every cell uses the canonical tagged Cell/Bits code
-- from ConcreteTapeCanonicalCellBitsExact.
--
-- The result is a literal Bits N assignment with exact width:
--
--   row:       |cells| * CellWidth
--   row pair:  (|before| + |after|) * CellWidth
--   run rows:  sum of row widths
--
-- The next remaining placement seam is coordinate-level: prove that pulling
-- this flat assignment back along each window's Fin-index renaming produces
-- exactly canonicalWindowCodec.encode(window).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Window
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Fixed-width list flattening
------------------------------------------------------------------------

encodeCells :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (cells :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  CNF.Bits
    (Canonical.listLength cells * Canonical.CellWidth machine)
encodeCells stateCoverage symbolCoverage [] =
  CNF.[]ᵇ
encodeCells {machine} stateCoverage symbolCoverage
    (cell ∷ cells) =
  Canonical.appendBits
    (Canonical.encodeCell stateCoverage symbolCoverage cell)
    (encodeCells stateCoverage symbolCoverage cells)

encodeRow :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine) →
  CNF.Bits
    (Canonical.listLength (Local.cells row) *
      Canonical.CellWidth machine)
encodeRow stateCoverage symbolCoverage row =
  encodeCells stateCoverage symbolCoverage (Local.cells row)

record FlatConcreteRowAssignment
    (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine) : Set where
  field
    width : Nat
    widthExact :
      width ≡
        Canonical.listLength (Local.cells row) *
        Canonical.CellWidth machine
    bits : CNF.Bits width

open FlatConcreteRowAssignment public

flatRowAssignment :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine) →
  FlatConcreteRowAssignment
    machine stateCoverage symbolCoverage row
flatRowAssignment stateCoverage symbolCoverage row = record
  { width =
      Canonical.listLength (Local.cells row) *
      Canonical.CellWidth _
  ; widthExact = refl
  ; bits = encodeRow stateCoverage symbolCoverage row
  }

------------------------------------------------------------------------
-- Two adjacent tableau rows are one literal assignment
------------------------------------------------------------------------

RowPairWidth :
  ∀ {machine} →
  Local.TapeRow machine →
  Local.TapeRow machine →
  Nat
RowPairWidth {machine} before after =
  Canonical.listLength (Local.cells before) *
      Canonical.CellWidth machine
  +
  Canonical.listLength (Local.cells after) *
      Canonical.CellWidth machine

encodeRowPair :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (before after : Local.TapeRow machine) →
  CNF.Bits (RowPairWidth before after)
encodeRowPair stateCoverage symbolCoverage before after =
  Canonical.appendBits
    (encodeRow stateCoverage symbolCoverage before)
    (encodeRow stateCoverage symbolCoverage after)

rowPairTakeBefore :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (before after : Local.TapeRow machine) →
  Canonical.takeBits
    (Canonical.listLength (Local.cells before) *
      Canonical.CellWidth machine)
    (encodeRowPair stateCoverage symbolCoverage before after)
  ≡ encodeRow stateCoverage symbolCoverage before
rowPairTakeBefore stateCoverage symbolCoverage before after =
  Canonical.takeAppendBits
    (encodeRow stateCoverage symbolCoverage before)
    (encodeRow stateCoverage symbolCoverage after)

rowPairDropBefore :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (before after : Local.TapeRow machine) →
  Canonical.dropBits
    (Canonical.listLength (Local.cells before) *
      Canonical.CellWidth machine)
    (encodeRowPair stateCoverage symbolCoverage before after)
  ≡ encodeRow stateCoverage symbolCoverage after
rowPairDropBefore stateCoverage symbolCoverage before after =
  Canonical.dropAppendBits
    (encodeRow stateCoverage symbolCoverage before)
    (encodeRow stateCoverage symbolCoverage after)

------------------------------------------------------------------------
-- Arbitrary finite row lists: one global Boolean assignment
------------------------------------------------------------------------

RowsWidth :
  ∀ {machine} →
  List (Local.TapeRow machine) →
  Nat
RowsWidth [] = zero
RowsWidth {machine} (row ∷ rows) =
  Canonical.listLength (Local.cells row) *
    Canonical.CellWidth machine
  + RowsWidth rows

encodeRows :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rows : List (Local.TapeRow machine)) →
  CNF.Bits (RowsWidth rows)
encodeRows stateCoverage symbolCoverage [] =
  CNF.[]ᵇ
encodeRows stateCoverage symbolCoverage (row ∷ rows) =
  Canonical.appendBits
    (encodeRow stateCoverage symbolCoverage row)
    (encodeRows stateCoverage symbolCoverage rows)

record FlatConcreteTableauAssignment
    (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rows : List (Local.TapeRow machine)) : Set where
  field
    width : Nat
    widthExact : width ≡ RowsWidth rows
    assignment : CNF.Bits width

open FlatConcreteTableauAssignment public

flatTableauAssignment :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rows : List (Local.TapeRow machine)) →
  FlatConcreteTableauAssignment
    machine stateCoverage symbolCoverage rows
flatTableauAssignment stateCoverage symbolCoverage rows = record
  { width = RowsWidth rows
  ; widthExact = refl
  ; assignment = encodeRows stateCoverage symbolCoverage rows
  }

headRowPullback :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine)
    (rows : List (Local.TapeRow machine)) →
  Canonical.takeBits
    (Canonical.listLength (Local.cells row) *
      Canonical.CellWidth machine)
    (encodeRows stateCoverage symbolCoverage (row ∷ rows))
  ≡ encodeRow stateCoverage symbolCoverage row
headRowPullback stateCoverage symbolCoverage row rows =
  Canonical.takeAppendBits
    (encodeRow stateCoverage symbolCoverage row)
    (encodeRows stateCoverage symbolCoverage rows)

tailRowsPullback :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine)
    (rows : List (Local.TapeRow machine)) →
  Canonical.dropBits
    (Canonical.listLength (Local.cells row) *
      Canonical.CellWidth machine)
    (encodeRows stateCoverage symbolCoverage (row ∷ rows))
  ≡ encodeRows stateCoverage symbolCoverage rows
tailRowsPullback stateCoverage symbolCoverage row rows =
  Canonical.dropAppendBits
    (encodeRow stateCoverage symbolCoverage row)
    (encodeRows stateCoverage symbolCoverage rows)

------------------------------------------------------------------------
-- The canonical six-cell encoding is literally six adjacent cell blocks
------------------------------------------------------------------------

encodeSixCells :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (window : Local.SixCellWindow machine) →
  CNF.Bits (Canonical.WindowWidth machine)
encodeSixCells stateCoverage symbolCoverage window =
  Canonical.appendBits cellOldLeft
    (Canonical.appendBits cellOldCenter
      (Canonical.appendBits cellOldRight
        (Canonical.appendBits cellNewLeft
          (Canonical.appendBits cellNewCenter cellNewRight))))
  where
    cellOldLeft =
      Canonical.encodeCell stateCoverage symbolCoverage
        (Local.oldLeft window)
    cellOldCenter =
      Canonical.encodeCell stateCoverage symbolCoverage
        (Local.oldCenter window)
    cellOldRight =
      Canonical.encodeCell stateCoverage symbolCoverage
        (Local.oldRight window)
    cellNewLeft =
      Canonical.encodeCell stateCoverage symbolCoverage
        (Local.newLeft window)
    cellNewCenter =
      Canonical.encodeCell stateCoverage symbolCoverage
        (Local.newCenter window)
    cellNewRight =
      Canonical.encodeCell stateCoverage symbolCoverage
        (Local.newRight window)

canonicalWindowEncoding_is_sixCellFlattening :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (window : Local.SixCellWindow machine) →
  Window.FixedWidthWindowCodec.encode
    (Canonical.canonicalWindowCodec machine stateCoverage symbolCoverage)
    window
  ≡ encodeSixCells stateCoverage symbolCoverage window
canonicalWindowEncoding_is_sixCellFlattening
    stateCoverage symbolCoverage
    (Local.six-cell-window
      oldLeft oldCenter oldRight
      newLeft newCenter newRight) =
  refl

record ConcreteTapeFlatAssignmentReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine)
    symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)

    canonicalCellBitsPaid : Bool
    flatRowAssignmentPaid : Bool
    flatRowPairAssignmentPaid : Bool
    flatFiniteTableauAssignmentPaid : Bool
    sixCellFlatteningPaid : Bool
    coordinateRenamingIntoGlobalAssignmentPaid : Bool
    endpointClausePlacementPaid : Bool
    acceptingRunIffSATPaid : Bool
    polynomialManyOneReductionPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeFlatAssignmentReceipt :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  ConcreteTapeFlatAssignmentReceipt machine
canonicalConcreteTapeFlatAssignmentReceipt machine stateCoverage symbolCoverage = record
  { stateCoverage = stateCoverage
  ; symbolCoverage = symbolCoverage
  ; canonicalCellBitsPaid = true
  ; flatRowAssignmentPaid = true
  ; flatRowPairAssignmentPaid = true
  ; flatFiniteTableauAssignmentPaid = true
  ; sixCellFlatteningPaid = true
  ; coordinateRenamingIntoGlobalAssignmentPaid = false
  ; endpointClausePlacementPaid = false
  ; acceptingRunIffSATPaid = false
  ; polynomialManyOneReductionPaid = false
  ; pVsNPResolved = false
  }
