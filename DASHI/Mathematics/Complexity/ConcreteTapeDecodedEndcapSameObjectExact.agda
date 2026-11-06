module DASHI.Mathematics.Complexity.ConcreteTapeDecodedEndcapSameObjectExact where

------------------------------------------------------------------------
-- ORIGINAL CANONICAL CELL BLOCKS ARE THE ACTUAL DECODED ROW CELLS.
--
-- We reuse Block.pullbackBlockRename_eq_blockSlice and the literal
-- Decode.decodeCells recursion, rather than adding a second decoder.
-- The all-rows SAT certificate yields FrontPlain and EndPlain on the
-- actual rowSliceBits of the SAME extended assignment.
--
-- No status Boolean, postulate, or foreign witness is admitted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Block
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalEndcapCNFExact as Endcap
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem

-- Lookup extensionality proves composition even when the two
-- placements are only propositionally, rather than definitionally,
-- equal. That is essential for the actual extended SAT assignment.
pullbackCompose :
  ∀ {m n k}
    (inner : Fin.Fin m → Fin.Fin n)
    (outer : Fin.Fin n → Fin.Fin k)
    (bits : CNF.Bits k) →
  Rename.pullbackBits inner (Rename.pullbackBits outer bits)
  ≡ Rename.pullbackBits (λ i → outer (inner i)) bits
pullbackCompose inner outer bits =
  lookupExt (λ i →
    trans
      (Rename.pullbackLookup inner (Rename.pullbackBits outer bits) i)
      (trans
        (Rename.pullbackLookup outer bits (inner i))
        (sym
          (Rename.pullbackLookup
            (λ j → outer (inner j)) bits i))))
  where
    lookupExt :
      ∀ {width} {left right : CNF.Bits width} →
      (∀ i → CNF.lookupBit left i ≡ CNF.lookupBit right i) →
      left ≡ right
    lookupExt {zero} {CNF.[]ᵇ} {CNF.[]ᵇ} pointwise = refl
    lookupExt {suc width} {x CNF.∷ᵇ xs} {y CNF.∷ᵇ ys}
        pointwise
      with pointwise Fin.zero
         | lookupExt (λ i → pointwise (Fin.suc i))
    ... | refl | refl = refl

-- Slot lookup in the original recursive decoder agrees with the
-- original block-slice operator, for arbitrary (even malformed) bits.
decodedCellAtBlockSlice :
  ∀ {machine count index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (slot : Global.Slot index count)
    (rowBits : CNF.Bits (Decode.RowBitsWidth machine count)) →
  Indexed.At index
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Block.blockSliceBits slot rowBits))
    (Decode.decodeCells stateCoverage symbolCoverage count rowBits)
decodedCellAtBlockSlice stateCoverage symbolCoverage
    Global.here rowBits = Indexed.here
decodedCellAtBlockSlice {machine}
    stateCoverage symbolCoverage
    (Global.there slot) rowBits =
  Indexed.there
    (decodedCellAtBlockSlice
      stateCoverage symbolCoverage slot
      (Canonical.dropBits (Canonical.CellWidth machine) rowBits))

decodedCellAtCanonicalBlock :
  ∀ {machine count index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (slot : Global.Slot index count)
    (rowBits : CNF.Bits (Decode.RowBitsWidth machine count)) →
  Indexed.At index
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Rename.pullbackBits (Global.blockRename slot) rowBits))
    (Decode.decodeCells stateCoverage symbolCoverage count rowBits)
decodedCellAtCanonicalBlock stateCoverage symbolCoverage slot rowBits =
  subst (λ cell → Indexed.At _ cell
            (Decode.decodeCells stateCoverage symbolCoverage _ rowBits))
    (sym (cong (Canonical.decodeCell stateCoverage symbolCoverage)
      (Block.pullbackBlockRename_eq_blockSlice slot rowBits)))
    (decodedCellAtBlockSlice
      stateCoverage symbolCoverage slot rowBits)

-- Plainness of the first/last decoded CELL (not merely a selected
-- Fin block) yields precisely the existing original boundary guards.
frontPlainFromFirstBlock :
  ∀ {machine} (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (n : Nat)
    (bits : CNF.Bits (Decode.RowBitsWidth machine (suc n))) →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Block.blockSliceBits Global.here bits)) →
  Pattern.FrontPlain
    (Decode.decodeCells stateCoverage symbolCoverage (suc n) bits)
frontPlainFromFirstBlock stateCoverage symbolCoverage n bits
    Pattern.is-plain = Pattern.frontCons

endPlainFromLastBlock :
  ∀ {machine} (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (n : Nat)
    (bits : CNF.Bits (Decode.RowBitsWidth machine (suc n))) →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Block.blockSliceBits (Endcap.lastPhysicalColumn n) bits)) →
  Pattern.EndPlain
    (Decode.decodeCells stateCoverage symbolCoverage (suc n) bits)
endPlainFromLastBlock stateCoverage symbolCoverage zero bits
    Pattern.is-plain = Pattern.endOne
endPlainFromLastBlock {machine} stateCoverage symbolCoverage
    (suc n) bits plain =
  Pattern.endMore
    (endPlainFromLastBlock
      stateCoverage symbolCoverage n
      (Canonical.dropBits (Canonical.CellWidth machine) bits)
      plain)

-- The selected cell of the EXACT original extended vector is
-- propositionally the selected cell of the original decoded row.
extendedRowCellSameObject :
  ∀ {machine steps count rowIndex cellIndex}
    (rowSlot : Global.Slot rowIndex (suc steps))
    (cellSlot : Global.Slot cellIndex count)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps count)) →
  Rename.pullbackBits
    (Endcap.rowCellExtendedRename rowSlot cellSlot) assignment
  ≡ Block.blockSliceBits cellSlot
      (Global.rowSliceBits rowSlot
        (FormulaSem.baseTraceBits assignment))
extendedRowCellSameObject rowSlot cellSlot assignment =
  trans
    (sym
      (pullbackCompose
        (Global.blockRename cellSlot)
        (λ i → Endpoint.liftBaseIndex (Global.globalRowRename rowSlot i))
        assignment))
    (trans
      (cong
        (Rename.pullbackBits (Global.blockRename cellSlot))
        (trans
          (sym (pullbackCompose
            (Global.globalRowRename rowSlot)
            Endpoint.liftBaseIndex assignment))
          refl))
      (Block.pullbackBlockRename_eq_blockSlice
        cellSlot
        (Global.rowSliceBits rowSlot
          (FormulaSem.baseTraceBits assignment))))

-- Both outer endcaps are reconstructed as literal predicates on the
-- original decoded row; use the existing all-row CNF certificate.
record DecodedRowEndcapsPlain
    {machine : Local.ConcreteTapeMachine}
    {steps rowIndex colsMinusOne : Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rowSlot : Global.Slot rowIndex (suc steps))
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) :
    Set where
  field
    front :
      Pattern.FrontPlain
        (Local.cells
          (Decode.decodeRow stateCoverage symbolCoverage
            (suc colsMinusOne)
            (Global.rowSliceBits rowSlot
              (FormulaSem.baseTraceBits assignment))))
    back :
      Pattern.EndPlain
        (Local.cells
          (Decode.decodeRow stateCoverage symbolCoverage
            (suc colsMinusOne)
            (Global.rowSliceBits rowSlot
              (FormulaSem.baseTraceBits assignment))))

open DecodedRowEndcapsPlain public

globalCNFToDecodedRowEndcaps :
  ∀ {machine steps rowIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (colsMinusOne : Nat)
    (rowSlot : Global.Slot rowIndex (suc steps))
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  CNF.evaluateCNF
    (Endcap.globalAllRowsEndcapsCNF colsMinusOne) assignment ≡ true →
  DecodedRowEndcapsPlain
    stateCoverage symbolCoverage rowSlot assignment
globalCNFToDecodedRowEndcaps
    stateCoverage symbolCoverage colsMinusOne
    rowSlot assignment accepted = record
  { front =
      frontPlainFromFirstBlock
        stateCoverage symbolCoverage colsMinusOne rowBits
        (subst
          (λ b → Pattern.IsPlainCell
            (Canonical.decodeCell stateCoverage symbolCoverage b))
          (extendedRowCellSameObject rowSlot Global.here assignment)
          (Endcap.firstPhysicalCellIsPlain plain))
  ; back =
      endPlainFromLastBlock
        stateCoverage symbolCoverage colsMinusOne rowBits
        (subst
          (λ b → Pattern.IsPlainCell
            (Canonical.decodeCell stateCoverage symbolCoverage b))
          (extendedRowCellSameObject
            rowSlot (Endcap.lastPhysicalColumn colsMinusOne) assignment)
          (Endcap.lastPhysicalCellIsPlain plain))
  }
  where
    rowBits =
      Global.rowSliceBits rowSlot
        (FormulaSem.baseTraceBits assignment)
    plain =
      Endcap.globalAllRowsEndcapsGivePhysicalRowPlain
        stateCoverage symbolCoverage colsMinusOne
        rowSlot assignment accepted
