module DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact where

------------------------------------------------------------------------
-- FIXED TRACE SLOT -> EXACT Fin PLACEMENT IN THE ONE GLOBAL SAT VECTOR
--
-- Global layout:
--
--   [ row₀ | row₁ | ... | row_T ] [ sel₀ | ... | sel_{T-1} ]
--
-- Every time-slot witness gives exact embeddings for:
--
--   row_t
--   row_{t+1}
--   selector_t
--
-- and therefore one combined local transition slice
--
--   selector_t || row_t || row_{t+1}
--
-- as a pullback from the single global assignment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Finite slot witnesses
------------------------------------------------------------------------

data Slot : Nat → Nat → Set where
  here :
    ∀ {remaining} →
    Slot zero (suc remaining)
  there :
    ∀ {index remaining} →
    Slot index remaining →
    Slot (suc index) (suc remaining)

sameSlotInSucc :
  ∀ {index count} →
  Slot index count →
  Slot index (suc count)
sameSlotInSucc here = here
sameSlotInSucc (there slot) =
  there (sameSlotInSucc slot)

nextSlotInSucc :
  ∀ {index count} →
  Slot index count →
  Slot (suc index) (suc count)
nextSlotInSucc slot =
  there slot

------------------------------------------------------------------------
-- Repeated fixed-width block placement
------------------------------------------------------------------------

blockRename :
  ∀ {index count width} →
  Slot index count →
  Fin.Fin width →
  Fin.Fin (count * width)
blockRename {width = width} here =
  Placement.finLeft
blockRename {width = width} (there slot) =
  λ i →
    Placement.finRight width
      (blockRename slot i)

rowBlockRename :
  ∀ {machine steps cols index} →
  Slot index (suc steps) →
  Fin.Fin (Decode.RowBitsWidth machine cols) →
  Fin.Fin (Trace.RowsTraceWidth machine steps cols)
rowBlockRename =
  blockRename

selectorBlockRename :
  ∀ {machine steps index} →
  Slot index steps →
  Fin.Fin (Selector.RuleWidth machine) →
  Fin.Fin (Trace.SelectorsTraceWidth machine steps)
selectorBlockRename =
  blockRename

------------------------------------------------------------------------
-- Lift row / selector blocks into the whole global trace vector
------------------------------------------------------------------------

globalRowRename :
  ∀ {machine steps cols index} →
  Slot index (suc steps) →
  Fin.Fin (Decode.RowBitsWidth machine cols) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
globalRowRename slot i =
  Placement.finLeft
    (rowBlockRename slot i)

globalSelectorRename :
  ∀ {machine steps cols index} →
  Slot index steps →
  Fin.Fin (Selector.RuleWidth machine) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
globalSelectorRename {machine} {steps} {cols} slot i =
  Placement.finRight
    (Trace.RowsTraceWidth machine steps cols)
    (selectorBlockRename slot i)

------------------------------------------------------------------------
-- One time step sees selector_t || row_t || row_{t+1}
------------------------------------------------------------------------

TransitionSliceWidth :
  (machine : Local.ConcreteTapeMachine) →
  (cols : Nat) →
  Nat
TransitionSliceWidth machine cols =
  Selector.RuleWidth machine +
  (Decode.RowBitsWidth machine cols +
   Decode.RowBitsWidth machine cols)

transitionRowPairRename :
  ∀ {machine steps cols index} →
  Slot index steps →
  Fin.Fin
    (Decode.RowBitsWidth machine cols +
     Decode.RowBitsWidth machine cols) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
transitionRowPairRename slot =
  Placement.finSumCases
    (globalRowRename (sameSlotInSucc slot))
    (globalRowRename (nextSlotInSucc slot))

transitionSliceRename :
  ∀ {machine steps cols index} →
  Slot index steps →
  Fin.Fin (TransitionSliceWidth machine cols) →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols)
transitionSliceRename slot =
  Placement.finSumCases
    (globalSelectorRename slot)
    (transitionRowPairRename slot)

transitionSliceBits :
  ∀ {machine steps cols index} →
  Slot index steps →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols) →
  CNF.Bits (TransitionSliceWidth machine cols)
transitionSliceBits slot globalBits =
  Rename.pullbackBits
    (transitionSliceRename slot)
    globalBits

rowSliceBits :
  ∀ {machine steps cols index} →
  Slot index (suc steps) →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols) →
  CNF.Bits (Decode.RowBitsWidth machine cols)
rowSliceBits slot globalBits =
  Rename.pullbackBits
    (globalRowRename slot)
    globalBits

selectorSliceBits :
  ∀ {machine steps cols index} →
  Slot index steps →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols) →
  CNF.Bits (Selector.RuleWidth machine)
selectorSliceBits slot globalBits =
  Rename.pullbackBits
    (globalSelectorRename slot)
    globalBits

------------------------------------------------------------------------
-- The combined transition pullback decomposes into the same global blocks
------------------------------------------------------------------------

transitionSlice_selector_lookup :
  ∀ {machine steps cols index}
    (slot : Slot index steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (i : Fin.Fin (Selector.RuleWidth machine)) →
  CNF.lookupBit
    (transitionSliceBits slot globalBits)
    (Placement.finLeft i)
  ≡ CNF.lookupBit
      (selectorSliceBits slot globalBits)
      i
transitionSlice_selector_lookup slot globalBits i =
  trans
    (Rename.pullbackLookup
      (transitionSliceRename slot) globalBits
      (Placement.finLeft i))
    (sym
      (Rename.pullbackLookup
        (globalSelectorRename slot) globalBits i))
  where
    trans :
      ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl refl = refl

    sym :
      ∀ {A : Set} {x y : A} →
      x ≡ y → y ≡ x
    sym refl = refl

transitionSlice_before_lookup :
  ∀ {machine steps cols index}
    (slot : Slot index steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (i : Fin.Fin (Decode.RowBitsWidth machine cols)) →
  CNF.lookupBit
    (transitionSliceBits slot globalBits)
    (Placement.finRight
      (Selector.RuleWidth machine)
      (Placement.finLeft i))
  ≡ CNF.lookupBit
      (rowSliceBits (sameSlotInSucc slot) globalBits)
      i
transitionSlice_before_lookup slot globalBits i =
  trans
    (Rename.pullbackLookup
      (transitionSliceRename slot) globalBits
      (Placement.finRight _ (Placement.finLeft i)))
    (sym
      (Rename.pullbackLookup
        (globalRowRename (sameSlotInSucc slot))
        globalBits i))
  where
    trans :
      ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl refl = refl

    sym :
      ∀ {A : Set} {x y : A} →
      x ≡ y → y ≡ x
    sym refl = refl

transitionSlice_after_lookup :
  ∀ {machine steps cols index}
    (slot : Slot index steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols))
    (i : Fin.Fin (Decode.RowBitsWidth machine cols)) →
  CNF.lookupBit
    (transitionSliceBits slot globalBits)
    (Placement.finRight
      (Selector.RuleWidth machine)
      (Placement.finRight
        (Decode.RowBitsWidth machine cols)
        i))
  ≡ CNF.lookupBit
      (rowSliceBits (nextSlotInSucc slot) globalBits)
      i
transitionSlice_after_lookup slot globalBits i =
  trans
    (Rename.pullbackLookup
      (transitionSliceRename slot) globalBits
      (Placement.finRight _ (Placement.finRight _ i)))
    (sym
      (Rename.pullbackLookup
        (globalRowRename (nextSlotInSucc slot))
        globalBits i))
  where
    trans :
      ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl refl = refl

    sym :
      ∀ {A : Set} {x y : A} →
      x ≡ y → y ≡ x
    sym refl = refl

record GlobalTracePlacementReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    rowBlockPlacementPaid : Bool
    selectorBlockPlacementPaid : Bool
    adjacentRowsPlacementPaid : Bool
    transitionSlicePlacementPaid : Bool
    selectorPullbackSameBlockPaid : Bool
    beforeRowPullbackSameBlockPaid : Bool
    afterRowPullbackSameBlockPaid : Bool
    transitionCNFPlacementPaid : Bool
    endpointPlacementPaid : Bool
    acceptingAssignmentIffRunPaid : Bool
    polynomialReductionPaid : Bool
    pVsNPResolved : Bool

globalTracePlacementReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  GlobalTracePlacementReceipt machine
globalTracePlacementReceipt machine = record
  { rowBlockPlacementPaid = true
  ; selectorBlockPlacementPaid = true
  ; adjacentRowsPlacementPaid = true
  ; transitionSlicePlacementPaid = true
  ; selectorPullbackSameBlockPaid = true
  ; beforeRowPullbackSameBlockPaid = true
  ; afterRowPullbackSameBlockPaid = true
  ; transitionCNFPlacementPaid = false
  ; endpointPlacementPaid = false
  ; acceptingAssignmentIffRunPaid = false
  ; polynomialReductionPaid = false
  ; pVsNPResolved = false
  }
