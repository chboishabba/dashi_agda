module DASHI.Mathematics.Complexity.ConcreteTapeInitialDecodeSameObjectExact where

------------------------------------------------------------------------
-- CANONICAL PADDED INPUT BITS DECODE BACK TO THE LITERAL PADDED INPUT ROW
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeInputPaddingExact as Padding
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
  Decode.decodeCells stateCoverage symbolCoverage
    (Canonical.listLength cells)
    (Flat.encodeCells stateCoverage symbolCoverage cells)
  ≡ cells
decodeCells_encodeCells stateCoverage symbolCoverage [] =
  refl
decodeCells_encodeCells {machine}
    stateCoverage symbolCoverage (cell ∷ cells)
    rewrite Canonical.takeAppendBits
      (Canonical.encodeCell stateCoverage symbolCoverage cell)
      (Flat.encodeCells stateCoverage symbolCoverage cells)
          | Canonical.dropAppendBits
              (Canonical.encodeCell stateCoverage symbolCoverage cell)
              (Flat.encodeCells stateCoverage symbolCoverage cells)
          | Canonical.decodeEncodeCell
              stateCoverage symbolCoverage cell
          | decodeCells_encodeCells
              stateCoverage symbolCoverage cells =
  refl

decodeRow_encodeRow :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine) →
  Decode.decodeRow stateCoverage symbolCoverage
    (Canonical.listLength (Local.cells row))
    (Flat.encodeRow stateCoverage symbolCoverage row)
  ≡ row
decodeRow_encodeRow stateCoverage symbolCoverage
    (Local.tape-row cells)
    rewrite decodeCells_encodeCells
      stateCoverage symbolCoverage cells =
  refl

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
    stateCoverage symbolCoverage input cols extension
    rewrite sym (Padding.paddedInitialRowAtWidth_count
      input cols extension) =
  Flat.encodeRow stateCoverage symbolCoverage
    (Padding.paddedInitialRowAtWidth input cols extension)

initialBitsDecodeToPaddedInputRow :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : Padding.WidthExtension input cols) →
  Decode.decodeRow stateCoverage symbolCoverage cols
    (paddedInitialBitsAtWidth
      stateCoverage symbolCoverage input cols extension)
  ≡
  Padding.paddedInitialRowAtWidth input cols extension
initialBitsDecodeToPaddedInputRow
    stateCoverage symbolCoverage input cols extension
    rewrite sym (Padding.paddedInitialRowAtWidth_count
      input cols extension) =
  decodeRow_encodeRow stateCoverage symbolCoverage
    (Padding.paddedInitialRowAtWidth input cols extension)

paddedInitialInterior :
  ∀ {machine}
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : Padding.WidthExtension input cols) →
  DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact.InitialInteriorRow
    machine
    (Padding.paddedInitialRowAtWidth input cols extension)
paddedInitialInterior {machine} input cols extension =
  record
    { DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact.interior =
        paddedInterior
    ; DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact.headIsInitial =
        refl
    }
  where
    open import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
    open import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Locality

    paddedInterior :
      Locality.InteriorHeadConfiguration machine
        (Padding.paddedInitialRowAtWidth input cols extension)
    paddedInterior =
      extendInterior
        (Input.initialInputInterior input)
        (Padding.extra extension)

    extendInterior :
      ∀ {row}
        (interior : Locality.InteriorHeadConfiguration machine row)
        (extra : Nat) →
      Locality.InteriorHeadConfiguration machine
        (Local.tape-row
          (Local.append (Local.cells row)
            (Padding.replicateBlank extra)))
    extendInterior interior extra = record
      { Locality.prefix = Locality.prefix interior
      ; Locality.suffix =
          Local.append
            (Locality.suffix interior)
            (Padding.replicateBlank extra)
      ; Locality.leftSymbol = Locality.leftSymbol interior
      ; Locality.readSymbol = Locality.readSymbol interior
      ; Locality.rightSymbol = Locality.rightSymbol interior
      ; Locality.headState = Locality.headState interior
      ; Locality.prefixPlain = Locality.prefixPlain interior
      ; Locality.suffixPlain =
          appendPlain
            (Locality.suffixPlain interior)
            (Padding.replicateBlankPlain extra)
      ; Locality.rowShape =
          appendInteriorShape
            (Locality.rowShape interior) extra
      }

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
          Local.cells row
          ≡ Local.append prefix
              (Local.plain left
                ∷ Local.headed q read
                ∷ Local.plain right
                ∷ suffix))
        (extra : Nat) →
      Local.append (Local.cells row) (Padding.replicateBlank extra)
      ≡
      Local.append prefix
        (Local.plain left
          ∷ Local.headed q read
          ∷ Local.plain right
          ∷ Local.append suffix (Padding.replicateBlank extra))
    appendInteriorShape refl extra =
      appendAssoc _ _ _
      where
        appendAssoc :
          ∀ {A : Set} (xs ys zs : List A) →
          Local.append (Local.append xs ys) zs
          ≡ Local.append xs (Local.append ys zs)
        appendAssoc [] ys zs = refl
        appendAssoc (x ∷ xs) ys zs
            rewrite appendAssoc xs ys zs =
          refl

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
