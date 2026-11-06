module DASHI.Mathematics.Complexity.ConcreteTapeInitialDecodeSameObjectExact where

------------------------------------------------------------------------
-- CANONICAL PADDED INPUT BITS DECODE BACK TO THE LITERAL PADDED INPUT ROW
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; cong₂; subst)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeInputPaddingExact as Padding
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Locality
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

decodeCells_encodeCells :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (cells :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  Decode.decodeCells {machine} stateCoverage symbolCoverage
    (Canonical.listLength cells)
    (Flat.encodeCells {machine} stateCoverage symbolCoverage cells)
  ≡ cells
decodeCells_encodeCells stateCoverage symbolCoverage [] =
  refl
decodeCells_encodeCells {machine}
    stateCoverage symbolCoverage (cell ∷ cells) =
  cong₂ _∷_
    (trans
      (cong (Canonical.decodeCell {machine} stateCoverage symbolCoverage)
        (Canonical.takeAppendBits
          (Canonical.encodeCell {machine} stateCoverage symbolCoverage cell)
          (Flat.encodeCells {machine} stateCoverage symbolCoverage cells)))
      (Canonical.decodeEncodeCell {machine} stateCoverage symbolCoverage cell))
    (trans
      (cong (Decode.decodeCells {machine} stateCoverage symbolCoverage (Canonical.listLength cells))
        (Canonical.dropAppendBits
          (Canonical.encodeCell {machine} stateCoverage symbolCoverage cell)
          (Flat.encodeCells {machine} stateCoverage symbolCoverage cells)))
      (decodeCells_encodeCells {machine} stateCoverage symbolCoverage cells))

decodeRow_encodeRow :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine) →
  Decode.decodeRow {machine} stateCoverage symbolCoverage
    (Canonical.listLength (Local.cells {machine} row))
    (Flat.encodeRow {machine} stateCoverage symbolCoverage row)
  ≡ row
decodeRow_encodeRow {machine} stateCoverage symbolCoverage
    (Local.tape-row cells) =
  cong (Local.tape-row {machine})
    (decodeCells_encodeCells {machine} stateCoverage symbolCoverage cells)

paddedInitialBitsAtWidth :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : Padding.WidthExtension input cols) →
  CNF.Bits (Decode.RowBitsWidth machine cols)
paddedInitialBitsAtWidth {machine}
    stateCoverage symbolCoverage input cols extension =
  subst CNF.Bits
    (cong (Decode.RowBitsWidth machine)
      (Padding.paddedInitialRowAtWidth_count input cols extension))
    (Flat.encodeRow {machine} stateCoverage symbolCoverage
      (Padding.paddedInitialRowAtWidth input cols extension))

initialBitsDecodeToPaddedInputRow_helper :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine)
    (cols : Nat)
    (e : Canonical.listLength (Local.cells {machine} row) ≡ cols) →
  Decode.decodeRow {machine} stateCoverage symbolCoverage cols
    (subst CNF.Bits (cong (Decode.RowBitsWidth machine) e)
      (Flat.encodeRow {machine} stateCoverage symbolCoverage row))
  ≡ row
initialBitsDecodeToPaddedInputRow_helper {machine} stateCoverage symbolCoverage row ._ refl =
  decodeRow_encodeRow {machine} stateCoverage symbolCoverage row

initialBitsDecodeToPaddedInputRow :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : Padding.WidthExtension input cols) →
  Decode.decodeRow {machine} stateCoverage symbolCoverage cols
    (paddedInitialBitsAtWidth {machine}
      stateCoverage symbolCoverage input cols extension)
  ≡
  Padding.paddedInitialRowAtWidth input cols extension
initialBitsDecodeToPaddedInputRow {machine}
    stateCoverage symbolCoverage input cols extension =
  initialBitsDecodeToPaddedInputRow_helper {machine}
    stateCoverage symbolCoverage
    (Padding.paddedInitialRowAtWidth input cols extension)
    cols
    (Padding.paddedInitialRowAtWidth_count input cols extension)

paddedInitialInterior :
  ∀ {machine}
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : Padding.WidthExtension input cols) →
  Accepting.InitialInteriorRow
    machine
    (Padding.paddedInitialRowAtWidth input cols extension)
paddedInitialInterior {machine} input cols extension =
  record
    { interior =
        paddedInterior
    ; headIsInitial =
        headIsInit input
    }
  where
    headIsInit :
      (inp : Input.InputWord machine) →
      Locality.headState (Input.initialInputInterior {machine} inp)
      ≡ Local.initialState machine
    headIsInit [] = refl
    headIsInit (x ∷ []) = refl
    headIsInit (x ∷ y ∷ rest) = refl
    appendPlain :
      ∀ {xs ys} →
      WF.PlainCells xs →
      WF.PlainCells ys →
      WF.PlainCells (Local.append xs ys)
    appendPlain WF.plainNil right = right
    appendPlain (WF.plainCons left) right =
      WF.plainCons (appendPlain left right)

    appendInteriorShape :
      ∀ {row prefix suffix left read right q}
        (shape :
          Local.cells {machine} row
          ≡ Local.append prefix
              (Local.plain left
                ∷ Local.headed q read
                ∷ Local.plain right
                ∷ suffix))
        (extra : Nat) →
      Local.append (Local.cells {machine} row) (Padding.replicateBlank {machine} extra)
      ≡
      Local.append prefix
        (Local.plain left
          ∷ Local.headed q read
          ∷ Local.plain right
          ∷ Local.append suffix (Padding.replicateBlank {machine} extra))
    appendInteriorShape {prefix = prefix} {suffix = suffix} {left = left} {read = read} {right = right} {q = q} refl extra =
      appendAssoc prefix (Local.plain left ∷ Local.headed q read ∷ Local.plain right ∷ suffix) (Padding.replicateBlank {machine} extra)
      where
        appendAssoc :
          ∀ {A : Set} (xs ys zs : List A) →
          Local.append (Local.append xs ys) zs
          ≡ Local.append xs (Local.append ys zs)
        appendAssoc [] ys zs = refl
        appendAssoc (x ∷ xs) ys zs
            rewrite appendAssoc xs ys zs =
          refl

    extendInterior :
      ∀ {row}
        (interior : Locality.InteriorHeadConfiguration machine row)
        (extra : Nat) →
      Locality.InteriorHeadConfiguration machine
        (Local.tape-row {machine}
          (Local.append (Local.cells {machine} row)
            (Padding.replicateBlank {machine} extra)))
    extendInterior interior extra = record
      { prefix = Locality.prefix interior
      ; suffix =
          Local.append
            (Locality.suffix interior)
            (Padding.replicateBlank {machine} extra)
      ; leftSymbol = Locality.leftSymbol interior
      ; readSymbol = Locality.readSymbol interior
      ; rightSymbol = Locality.rightSymbol interior
      ; headState = Locality.headState interior
      ; prefixPlain = Locality.prefixPlain interior
      ; suffixPlain =
          appendPlain
            (Locality.suffixPlain interior)
            (Padding.replicateBlankPlain {machine} extra)
      ; rowShape =
          appendInteriorShape
            (Locality.rowShape interior) extra
      }

    paddedInterior :
      Locality.InteriorHeadConfiguration machine
        (Padding.paddedInitialRowAtWidth {machine} input cols extension)
    paddedInterior =
      extendInterior
        (Input.initialInputInterior {machine} input)
        (Padding.extra extension)

record InitialDecodeSameObjectReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    rowDecodeEncodePaid : Bool
    paddedBitsAtExactWidthPaid : Bool
    paddedBitsDecodeToLiteralRowPaid : Bool
    paddedLiteralRowInitialInteriorPaid : Bool
    endpointEqualityToLiteralInputPaid : Bool

initialDecodeSameObjectReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  InitialDecodeSameObjectReceipt machine
initialDecodeSameObjectReceipt machine = record
  { rowDecodeEncodePaid = true
  ; paddedBitsAtExactWidthPaid = true
  ; paddedBitsDecodeToLiteralRowPaid = true
  ; paddedLiteralRowInitialInteriorPaid = true
  ; endpointEqualityToLiteralInputPaid = false
  }
