module DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact where

------------------------------------------------------------------------
-- GLOBAL FIN BLOCK PULLBACK = REPEATED TAKE/DROP SLICE
--
-- The global decoder partitions vectors by repeated takeBits/dropBits.
-- The placed CNFs address the same vectors by repeated Fin block embeddings.
-- This file proves those two views of the same global assignment are literally
-- equal bit vectors.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (trans; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

lookupTakeBits :
  ∀ {m n}
    (bits : CNF.Bits (m + n))
    (i : Fin.Fin m) →
  CNF.lookupBit (Canonical.takeBits m bits) i
  ≡ CNF.lookupBit bits (Placement.finLeft i)
lookupTakeBits {zero} bits ()
lookupTakeBits {suc m} (bit CNF.∷ᵇ bits) Fin.zero =
  refl
lookupTakeBits {suc m} (bit CNF.∷ᵇ bits) (Fin.suc i) =
  lookupTakeBits bits i

lookupDropBits :
  ∀ {m n}
    (bits : CNF.Bits (m + n))
    (i : Fin.Fin n) →
  CNF.lookupBit (Canonical.dropBits m bits) i
  ≡ CNF.lookupBit bits (Placement.finRight m i)
lookupDropBits {zero} bits i =
  refl
lookupDropBits {suc m} (bit CNF.∷ᵇ bits) i =
  lookupDropBits bits i

pullbackFinLeft_eq_takeBits :
  ∀ {m n}
    (bits : CNF.Bits (m + n)) →
  Rename.pullbackBits Placement.finLeft bits
  ≡ Canonical.takeBits m bits
pullbackFinLeft_eq_takeBits bits =
  Placement.bitsExt
    (λ i →
      trans
        (Rename.pullbackLookup Placement.finLeft bits i)
        (sym (lookupTakeBits bits i)))

pullbackFinRight_eq_dropBits :
  ∀ {m n}
    (bits : CNF.Bits (m + n)) →
  Rename.pullbackBits (Placement.finRight m) bits
  ≡ Canonical.dropBits m bits
pullbackFinRight_eq_dropBits bits =
  Placement.bitsExt
    (λ i →
      trans
        (Rename.pullbackLookup (Placement.finRight _) bits i)
        (sym (lookupDropBits bits i)))

blockSliceBits :
  ∀ {index count width} →
  Global.Slot index count →
  CNF.Bits (count * width) →
  CNF.Bits width
blockSliceBits {width = width} Global.here bits =
  Canonical.takeBits width bits
blockSliceBits {width = width} (Global.there slot) bits =
  blockSliceBits slot
    (Canonical.dropBits width bits)

pullbackBlockRename_eq_blockSlice :
  ∀ {index count width}
    (slot : Global.Slot index count)
    (bits : CNF.Bits (count * width)) →
  Rename.pullbackBits (Global.blockRename slot) bits
  ≡ blockSliceBits slot bits
pullbackBlockRename_eq_blockSlice
    {width = width} Global.here bits =
  pullbackFinLeft_eq_takeBits bits
pullbackBlockRename_eq_blockSlice
    {width = width} (Global.there slot) bits =
  Placement.bitsExt pointwise
  where
    tailBits =
      Canonical.dropBits width bits

    ih =
      pullbackBlockRename_eq_blockSlice slot tailBits

    pointwise :
      ∀ i →
      CNF.lookupBit
        (Rename.pullbackBits
          (Global.blockRename (Global.there slot))
          bits)
        i
      ≡
      CNF.lookupBit
        (blockSliceBits (Global.there slot) bits)
        i
    pointwise i =
      trans
        (Rename.pullbackLookup
          (Global.blockRename (Global.there slot))
          bits i)
        (trans
          (sym (lookupDropBits bits
            (Global.blockRename slot i)))
          (trans
            (sym
              (Rename.pullbackLookup
                (Global.blockRename slot)
                tailBits i))
            (congLookup ih i)))
      where
        congLookup :
          ∀ {n} {left right : CNF.Bits n} →
          left ≡ right →
          (j : Fin.Fin n) →
          CNF.lookupBit left j ≡ CNF.lookupBit right j
        congLookup refl j = refl

rowsPrefixBits :
  ∀ {machine steps cols} →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols) →
  CNF.Bits (Trace.RowsTraceWidth machine steps cols)
rowsPrefixBits {machine} {steps} {cols} bits =
  Canonical.takeBits
    (Trace.RowsTraceWidth machine steps cols)
    bits

selectorsSuffixBits :
  ∀ {machine steps cols} →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols) →
  CNF.Bits (Trace.SelectorsTraceWidth machine steps)
selectorsSuffixBits {machine} {steps} {cols} bits =
  Canonical.dropBits
    (Trace.RowsTraceWidth machine steps cols)
    bits

rowSliceBits_eq_blockSlice :
  ∀ {machine steps cols index}
    (slot : Global.Slot index (suc steps))
    (globalBits :
      CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Global.rowSliceBits slot globalBits
  ≡
  blockSliceBits slot (rowsPrefixBits globalBits)
rowSliceBits_eq_blockSlice {machine} {steps} {cols}
    slot globalBits =
  Placement.bitsExt pointwise
  where
    rowWidth = Decode.RowBitsWidth machine cols
    rowsBits = rowsPrefixBits globalBits

    blockEq :
      Rename.pullbackBits
        (Global.rowBlockRename slot)
        rowsBits
      ≡ blockSliceBits slot rowsBits
    blockEq =
      pullbackBlockRename_eq_blockSlice slot rowsBits

    pointwise :
      ∀ i →
      CNF.lookupBit (Global.rowSliceBits slot globalBits) i
      ≡ CNF.lookupBit (blockSliceBits slot rowsBits) i
    pointwise i =
      trans
        (Rename.pullbackLookup
          (Global.globalRowRename slot) globalBits i)
        (trans
          (sym
            (lookupTakeBits globalBits
              (Global.rowBlockRename slot i)))
          (trans
            (sym
              (Rename.pullbackLookup
                (Global.rowBlockRename slot)
                rowsBits i))
            (congLookup blockEq i)))
      where
        congLookup :
          ∀ {n} {left right : CNF.Bits n} →
          left ≡ right →
          (j : Fin.Fin n) →
          CNF.lookupBit left j ≡ CNF.lookupBit right j
        congLookup refl j = refl

selectorSliceBits_eq_blockSlice :
  ∀ {machine steps cols index}
    (slot : Global.Slot index steps)
    (globalBits :
      CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Global.selectorSliceBits slot globalBits
  ≡
  blockSliceBits slot (selectorsSuffixBits globalBits)
selectorSliceBits_eq_blockSlice {machine} {steps} {cols}
    slot globalBits =
  Placement.bitsExt pointwise
  where
    selectorBits = selectorsSuffixBits globalBits

    blockEq :
      Rename.pullbackBits
        (Global.selectorBlockRename slot)
        selectorBits
      ≡ blockSliceBits slot selectorBits
    blockEq =
      pullbackBlockRename_eq_blockSlice slot selectorBits

    pointwise :
      ∀ i →
      CNF.lookupBit (Global.selectorSliceBits slot globalBits) i
      ≡ CNF.lookupBit (blockSliceBits slot selectorBits) i
    pointwise i =
      trans
        (Rename.pullbackLookup
          (Global.globalSelectorRename slot) globalBits i)
        (trans
          (sym
            (lookupDropBits globalBits
              (Global.selectorBlockRename slot i)))
          (trans
            (sym
              (Rename.pullbackLookup
                (Global.selectorBlockRename slot)
                selectorBits i))
            (congLookup blockEq i)))
      where
        congLookup :
          ∀ {n} {left right : CNF.Bits n} →
          left ≡ right →
          (j : Fin.Fin n) →
          CNF.lookupBit left j ≡ CNF.lookupBit right j
        congLookup refl j = refl

record GlobalBlockSliceConsistencyReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    takeMatchesLeftFinPullbackPaid : Bool
    dropMatchesRightFinPullbackPaid : Bool
    repeatedBlockPullbackPaid : Bool
    rowSliceMatchesDecoderPartitionPaid : Bool
    selectorSliceMatchesDecoderPartitionPaid : Bool
    rawWindowMatchesDecodedRowsPaid : Bool
    semanticScanToStepsPaid : Bool

globalBlockSliceConsistencyReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  GlobalBlockSliceConsistencyReceipt machine
globalBlockSliceConsistencyReceipt machine = record
  { takeMatchesLeftFinPullbackPaid = true
  ; dropMatchesRightFinPullbackPaid = true
  ; repeatedBlockPullbackPaid = true
  ; rowSliceMatchesDecoderPartitionPaid = true
  ; selectorSliceMatchesDecoderPartitionPaid = true
  ; rawWindowMatchesDecodedRowsPaid = Agda.Builtin.Bool.false
  ; semanticScanToStepsPaid = Agda.Builtin.Bool.false
  }
