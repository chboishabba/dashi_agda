module DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact where

------------------------------------------------------------------------
-- INDEXED CONCRETE WINDOW -> GLOBAL FLAT-ASSIGNMENT VARIABLE RENAMING
--
-- Every inductive At-witness for a concrete tape cell determines the exact
-- block of CellWidth bits occupied by that cell in encodeRow.  We prove the
-- lookup law directly, then combine the six cell blocks of an indexed 2x3
-- window across the flattened before/after row pair.
--
-- Result:
--
--   ∃ rename : Fin WindowWidth -> Fin RowPairWidth
--
-- such that pullbackBits rename (encodeRowPair before after) is literally the
-- canonical six-cell window encoding consumed by the existing placed-CNF
-- compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Window

------------------------------------------------------------------------
-- Fin embeddings for concatenated bit vectors
------------------------------------------------------------------------

finLeft :
  ∀ {m n : Nat} →
  Fin.Fin m →
  Fin.Fin (m + n)
finLeft {zero} ()
finLeft {suc m} Fin.zero = Fin.zero
finLeft {suc m} (Fin.suc i) = Fin.suc (finLeft i)

finRight :
  ∀ (m : Nat) {n : Nat} →
  Fin.Fin n →
  Fin.Fin (m + n)
finRight zero i = i
finRight (suc m) i = Fin.suc (finRight m i)

lookupAppendLeft :
  ∀ {m n : Nat}
    (left : CNF.Bits m)
    (right : CNF.Bits n)
    (i : Fin.Fin m) →
  CNF.lookupBit
    (Canonical.appendBits left right)
    (finLeft i)
  ≡ CNF.lookupBit left i
lookupAppendLeft CNF.[]ᵇ right ()
lookupAppendLeft (bit CNF.∷ᵇ left) right Fin.zero = refl
lookupAppendLeft (bit CNF.∷ᵇ left) right (Fin.suc i) =
  lookupAppendLeft left right i

lookupAppendRight :
  ∀ {m n : Nat}
    (left : CNF.Bits m)
    (right : CNF.Bits n)
    (i : Fin.Fin n) →
  CNF.lookupBit
    (Canonical.appendBits left right)
    (finRight m i)
  ≡ CNF.lookupBit right i
lookupAppendRight CNF.[]ᵇ right i = refl
lookupAppendRight (bit CNF.∷ᵇ left) right i =
  lookupAppendRight left right i

finSumCases :
  ∀ {m n global : Nat} →
  (Fin.Fin m → Fin.Fin global) →
  (Fin.Fin n → Fin.Fin global) →
  Fin.Fin (m + n) →
  Fin.Fin global
finSumCases {zero} left right i = right i
finSumCases {suc m} left right Fin.zero = left Fin.zero
finSumCases {suc m} left right (Fin.suc i) =
  finSumCases
    (λ j → left (Fin.suc j))
    right
    i

finSumCases_left :
  ∀ {m n global : Nat}
    (left : Fin.Fin m → Fin.Fin global)
    (right : Fin.Fin n → Fin.Fin global)
    (i : Fin.Fin m) →
  finSumCases left right (finLeft i) ≡ left i
finSumCases_left {zero} left right ()
finSumCases_left {suc m} left right Fin.zero = refl
finSumCases_left {suc m} left right (Fin.suc i) =
  finSumCases_left
    (λ j → left (Fin.suc j))
    right i

finSumCases_right :
  ∀ {m n global : Nat}
    (left : Fin.Fin m → Fin.Fin global)
    (right : Fin.Fin n → Fin.Fin global)
    (i : Fin.Fin n) →
  finSumCases left right (finRight m i) ≡ right i
finSumCases_right {zero} left right i = refl
finSumCases_right {suc m} left right i =
  finSumCases_right
    (λ j → left (Fin.suc j))
    right i

bitsExt :
  ∀ {n : Nat} {left right : CNF.Bits n} →
  ((i : Fin.Fin n) →
    CNF.lookupBit left i ≡ CNF.lookupBit right i) →
  left ≡ right
bitsExt {zero} {CNF.[]ᵇ} {CNF.[]ᵇ} pointwise = refl
bitsExt {suc n}
    {leftHead CNF.∷ᵇ leftTail}
    {rightHead CNF.∷ᵇ rightTail}
    pointwise
    with pointwise Fin.zero
       | bitsExt
          (λ i → pointwise (Fin.suc i))
... | refl | refl = refl

------------------------------------------------------------------------
-- Generic placement of one local bit vector inside one global bit vector
------------------------------------------------------------------------

record BitsPlacement
    {local global : Nat}
    (localBits : CNF.Bits local)
    (globalBits : CNF.Bits global) : Set where
  field
    rename : Fin.Fin local → Fin.Fin global
    lookupCorrect :
      (i : Fin.Fin local) →
      CNF.lookupBit globalBits (rename i)
      ≡ CNF.lookupBit localBits i

open BitsPlacement public

placementLeft :
  ∀ {m n : Nat}
    (left : CNF.Bits m)
    (right : CNF.Bits n) →
  BitsPlacement left (Canonical.appendBits left right)
placementLeft left right = record
  { rename = finLeft
  ; lookupCorrect = lookupAppendLeft left right
  }

placementRight :
  ∀ {m n : Nat}
    (left : CNF.Bits m)
    (right : CNF.Bits n) →
  BitsPlacement right (Canonical.appendBits left right)
placementRight left right = record
  { rename = finRight m
  ; lookupCorrect = lookupAppendRight left right
  }

composePlacement :
  ∀ {a b c : Nat}
    {small : CNF.Bits a}
    {middle : CNF.Bits b}
    {large : CNF.Bits c} →
  BitsPlacement small middle →
  BitsPlacement middle large →
  BitsPlacement small large
composePlacement first second = record
  { rename = λ i → rename second (rename first i)
  ; lookupCorrect = λ i →
      trans
        (lookupCorrect second (rename first i))
        (lookupCorrect first i)
  }

appendPlacement :
  ∀ {m n global : Nat}
    {left : CNF.Bits m}
    {right : CNF.Bits n}
    {globalBits : CNF.Bits global} →
  BitsPlacement left globalBits →
  BitsPlacement right globalBits →
  BitsPlacement
    (Canonical.appendBits left right)
    globalBits
appendPlacement leftPlaced rightPlaced = record
  { rename =
      finSumCases
        (rename leftPlaced)
        (rename rightPlaced)
  ; lookupCorrect =
      pointwise
  }
  where
    pointwise :
      (i : Fin.Fin _) →
      CNF.lookupBit _
        (finSumCases
          (rename leftPlaced)
          (rename rightPlaced)
          i)
      ≡ CNF.lookupBit
          (Canonical.appendBits _ _)
          i
    pointwise {m = zero} i =
      lookupCorrect rightPlaced i
    pointwise {m = suc m} Fin.zero =
      lookupCorrect leftPlaced Fin.zero
    pointwise {m = suc m} (Fin.suc i)
      with i
    ... | i' =
      pointwiseTail i'
      where
        pointwiseTail :
          (j : Fin.Fin (m + _)) →
          CNF.lookupBit _
            (finSumCases
              (λ k → rename leftPlaced (Fin.suc k))
              (rename rightPlaced)
              j)
          ≡ CNF.lookupBit
              (Canonical.appendBits
                (tailBits _)
                _)
              j
        pointwiseTail = appendTailCorrect leftPlaced rightPlaced

        tailBits :
          ∀ {k} → CNF.Bits (suc k) → CNF.Bits k
        tailBits (b CNF.∷ᵇ bs) = bs

        appendTailCorrect :
          ∀ {k n g}
            {l : CNF.Bits (suc k)}
            {r : CNF.Bits n}
            {G : CNF.Bits g} →
          BitsPlacement l G →
          BitsPlacement r G →
          (j : Fin.Fin (k + n)) →
          CNF.lookupBit G
            (finSumCases
              (λ t → rename leftPlaced (Fin.suc t))
              (rename rightPlaced)
              j)
          ≡ CNF.lookupBit
              (Canonical.appendBits (tailBits l) r)
              j
        appendTailCorrect {zero} lp rp j =
          lookupCorrect rp j
        appendTailCorrect {suc k} lp rp Fin.zero =
          lookupCorrect lp (Fin.suc Fin.zero)
        appendTailCorrect {suc k} lp rp (Fin.suc j) =
          appendTailCorrect
            {k}
            (record
              { rename = λ t → rename lp (Fin.suc t)
              ; lookupCorrect = λ t → lookupCorrect lp (Fin.suc t)
              })
            rp j

pullbackPlacement :
  ∀ {local global}
    {localBits : CNF.Bits local}
    {globalBits : CNF.Bits global}
    (placement : BitsPlacement localBits globalBits) →
  Rename.pullbackBits (rename placement) globalBits
  ≡ localBits
pullbackPlacement placement =
  bitsExt λ i →
    trans
      (Rename.pullbackLookup
        (rename placement) _ i)
      (lookupCorrect placement i)

------------------------------------------------------------------------
-- One At-witness gives one exact cell block in the flattened row
------------------------------------------------------------------------

cellPlacementAt :
  ∀ {machine index cell cells}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Indexed.At index cell cells →
  BitsPlacement
    (Canonical.encodeCell stateCoverage symbolCoverage cell)
    (Flat.encodeCells stateCoverage symbolCoverage cells)
cellPlacementAt stateCoverage symbolCoverage Indexed.here =
  placementLeft
    (Canonical.encodeCell stateCoverage symbolCoverage _)
    (Flat.encodeCells stateCoverage symbolCoverage _)
cellPlacementAt stateCoverage symbolCoverage
    (Indexed.there membership) =
  composePlacement
    (cellPlacementAt stateCoverage symbolCoverage membership)
    (placementRight
      (Canonical.encodeCell stateCoverage symbolCoverage _)
      (Flat.encodeCells stateCoverage symbolCoverage _))

------------------------------------------------------------------------
-- Lift cell placements into the whole before/after row-pair assignment
------------------------------------------------------------------------

beforeCellPlacement :
  ∀ {machine before after index cell}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Indexed.At index cell (Local.cells before) →
  BitsPlacement
    (Canonical.encodeCell stateCoverage symbolCoverage cell)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
beforeCellPlacement stateCoverage symbolCoverage membership =
  composePlacement
    (cellPlacementAt stateCoverage symbolCoverage membership)
    (placementLeft
      (Flat.encodeRow stateCoverage symbolCoverage _)
      (Flat.encodeRow stateCoverage symbolCoverage _))

afterCellPlacement :
  ∀ {machine before after index cell}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Indexed.At index cell (Local.cells after) →
  BitsPlacement
    (Canonical.encodeCell stateCoverage symbolCoverage cell)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
afterCellPlacement stateCoverage symbolCoverage membership =
  composePlacement
    (cellPlacementAt stateCoverage symbolCoverage membership)
    (placementRight
      (Flat.encodeRow stateCoverage symbolCoverage _)
      (Flat.encodeRow stateCoverage symbolCoverage _))

------------------------------------------------------------------------
-- Exact six-cell placement for an IndexedSixCellWindow
------------------------------------------------------------------------

indexedWindowBitsPlacement :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  BitsPlacement
    (Flat.encodeSixCells stateCoverage symbolCoverage
      (Indexed.forgetIndex occurrence))
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
indexedWindowBitsPlacement
    stateCoverage symbolCoverage occurrence =
  appendPlacement oldLeftPlaced
    (appendPlacement oldCenterPlaced
      (appendPlacement oldRightPlaced
        (appendPlacement newLeftPlaced
          (appendPlacement newCenterPlaced newRightPlaced))))
  where
    oldTriple = Indexed.oldTriple occurrence
    newTriple = Indexed.newTriple occurrence

    oldLeftPlaced =
      beforeCellPlacement stateCoverage symbolCoverage
        (Indexed.leftAt oldTriple)
    oldCenterPlaced =
      beforeCellPlacement stateCoverage symbolCoverage
        (Indexed.centerAt oldTriple)
    oldRightPlaced =
      beforeCellPlacement stateCoverage symbolCoverage
        (Indexed.rightAt oldTriple)

    newLeftPlaced =
      afterCellPlacement stateCoverage symbolCoverage
        (Indexed.leftAt newTriple)
    newCenterPlaced =
      afterCellPlacement stateCoverage symbolCoverage
        (Indexed.centerAt newTriple)
    newRightPlaced =
      afterCellPlacement stateCoverage symbolCoverage
        (Indexed.rightAt newTriple)

indexedWindowRename :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  Fin.Fin (Canonical.WindowWidth machine) →
  Fin.Fin (Flat.RowPairWidth before after)
indexedWindowRename stateCoverage symbolCoverage occurrence =
  rename
    (indexedWindowBitsPlacement
      stateCoverage symbolCoverage occurrence)

indexedWindowPullback_is_sixCellEncoding :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  Rename.pullbackBits
    (indexedWindowRename stateCoverage symbolCoverage occurrence)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
  ≡ Flat.encodeSixCells stateCoverage symbolCoverage
      (Indexed.forgetIndex occurrence)
indexedWindowPullback_is_sixCellEncoding
    stateCoverage symbolCoverage occurrence =
  pullbackPlacement
    (indexedWindowBitsPlacement
      stateCoverage symbolCoverage occurrence)

indexedWindowPullback_is_canonicalWindowEncoding :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  Rename.pullbackBits
    (indexedWindowRename stateCoverage symbolCoverage occurrence)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
  ≡ Window.FixedWidthWindowCodec.encode
      (Canonical.canonicalWindowCodec
        machine stateCoverage symbolCoverage)
      (Indexed.forgetIndex occurrence)
indexedWindowPullback_is_canonicalWindowEncoding
    stateCoverage symbolCoverage occurrence =
  trans
    (indexedWindowPullback_is_sixCellEncoding
      stateCoverage symbolCoverage occurrence)
    (sym
      (Flat.canonicalWindowEncoding_is_sixCellFlattening
        stateCoverage symbolCoverage
        (Indexed.forgetIndex occurrence)))

record CanonicalWindowPlacementReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine)
    symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)

    canonicalCellBitsPaid : Bool
    flatGlobalAssignmentPaid : Bool
    indexedWindowFinRenamingPaid : Bool
    pullbackEqualsCanonicalWindowBitsPaid : Bool
    placedLocalCNFWeldPaid : Bool
    endpointClausePlacementPaid : Bool
    acceptingRunIffSATPaid : Bool
    polynomialManyOneReductionPaid : Bool
    pVsNPResolved : Bool

canonicalWindowPlacementReceipt :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CanonicalWindowPlacementReceipt machine
canonicalWindowPlacementReceipt machine stateCoverage symbolCoverage = record
  { stateCoverage = stateCoverage
  ; symbolCoverage = symbolCoverage
  ; canonicalCellBitsPaid = true
  ; flatGlobalAssignmentPaid = true
  ; indexedWindowFinRenamingPaid = true
  ; pullbackEqualsCanonicalWindowBitsPaid = true
  ; placedLocalCNFWeldPaid = false
  ; endpointClausePlacementPaid = false
  ; acceptingRunIffSATPaid = false
  ; polynomialManyOneReductionPaid = false
  ; pVsNPResolved = false
  }
