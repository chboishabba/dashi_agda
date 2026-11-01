module DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyRoundTripExact where

------------------------------------------------------------------------
-- PROOF-FREE KEY REINSERTION
--
-- A residual key stores (mu,v,j,u), with k=j+1.  Reinsertion adds k copies at
-- coordinate v.  The predecessor j is automatically a valid occurrence in the
-- reconstructed multiplicity because j < mu_v + (j+1).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (Fin; fromℕ<; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteNatVectorCoordinateUpdateExact as Update
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition

------------------------------------------------------------------------
-- Elementary bound j < m + (j+1).

predecessorBelowInserted :
  (existing predecessor : Nat) →
  predecessor < existing + suc predecessor
predecessorBelowInserted zero predecessor = NatP.≤-refl
predecessorBelowInserted (suc existing) predecessor =
  NatP.≤-step (predecessorBelowInserted existing predecessor)

------------------------------------------------------------------------
-- Reconstruct the source vector and the marked occurrence.

insertedVector :
  ∀ {n} → Key.ResidualKey n → Vec Nat n
insertedVector residual =
  Update.addAt
    (Key.residualCopies residual)
    (Key.residualIndex residual)
    (Key.residualVector residual)

insertedOccurrenceBound :
  ∀ {n} (residual : Key.ResidualKey n) →
  Key.residualPredecessor residual
  < Partition.lookupMultiplicity
      (Key.residualIndex residual)
      (insertedVector residual)
insertedOccurrenceBound residual =
  subst
    (λ target → Key.residualPredecessor residual < target)
    (sym
      (Update.lookupAddAt
        (Key.residualCopies residual)
        (Key.residualIndex residual)
        (Key.residualVector residual)))
    (predecessorBelowInserted
      (Partition.lookupMultiplicity
        (Key.residualIndex residual)
        (Key.residualVector residual))
      (Key.residualPredecessor residual))

insertedOccurrence :
  ∀ {n} (residual : Key.ResidualKey n) →
  Fin
    (Partition.lookupMultiplicity
      (Key.residualIndex residual)
      (insertedVector residual))
insertedOccurrence residual = fromℕ< (insertedOccurrenceBound residual)

insertKey :
  ∀ {n} → Key.ResidualKey n → Key.CellKey n
insertKey residual =
  insertedVector residual
  , Key.residualIndex residual
  , insertedOccurrence residual
  , Key.residualUnit residual

insertedOccurrenceToNat :
  ∀ {n} (residual : Key.ResidualKey n) →
  toℕ (insertedOccurrence residual)
  ≡ Key.residualPredecessor residual
insertedOccurrenceToNat residual =
  FinP.toℕ-fromℕ< (insertedOccurrenceBound residual)

------------------------------------------------------------------------
-- Delete then reinsert recovers the source multiplicity vector exactly.

cellCopiesAvailable :
  ∀ {n} (cell : Key.CellKey n) →
  Key.cellCopies cell
  ≤ Partition.lookupMultiplicity (Key.cellIndex cell) (Key.cellVector cell)
cellCopiesAvailable cell = FinP.toℕ<n (Key.cellOccurrence cell)

insertDeleteVector :
  ∀ {n} (cell : Key.CellKey n) →
  Key.cellVector (insertKey (Key.deleteKey cell))
  ≡ Key.cellVector cell
insertDeleteVector cell =
  Update.addAfterSubtractAt
    (Key.cellCopies cell)
    (Key.cellIndex cell)
    (Key.cellVector cell)
    (cellCopiesAvailable cell)

insertDeletePredecessor :
  ∀ {n} (cell : Key.CellKey n) →
  Key.residualPredecessor (Key.deleteKey cell)
  ≡ toℕ (Key.cellOccurrence cell)
insertDeletePredecessor cell = refl

insertDeleteIndex :
  ∀ {n} (cell : Key.CellKey n) →
  Key.residualIndex (Key.deleteKey cell) ≡ Key.cellIndex cell
insertDeleteIndex cell = refl

insertDeleteUnit :
  ∀ {n} (cell : Key.CellKey n) →
  Key.residualUnit (Key.deleteKey cell) ≡ Key.cellUnit cell
insertDeleteUnit cell = refl

------------------------------------------------------------------------
-- Full literal cell-key round trip.  Once the source vector is rewritten by
-- the add-after-subtract theorem, the only non-definitional coordinate is the
-- reconstructed occurrence; Fin.toNat injectivity closes it.

insertDeleteKey :
  ∀ {n} (cell : Key.CellKey n) →
  insertKey (Key.deleteKey cell) ≡ cell
insertDeleteKey (vector , index , occurrence , unit)
  with insertDeleteVector (vector , index , occurrence , unit)
... | refl =
  cong
    (λ recoveredOccurrence → vector , index , recoveredOccurrence , unit)
    (FinP.toℕ-injective
      (insertedOccurrenceToNat
        (Key.deleteKey (vector , index , occurrence , unit))))

deleteKeyInjective :
  ∀ {n} {left right : Key.CellKey n} →
  Key.deleteKey left ≡ Key.deleteKey right → left ≡ right
deleteKeyInjective {left = left} {right = right} equality =
  trans
    (sym (insertDeleteKey left))
    (trans
      (cong insertKey equality)
      (insertDeleteKey right))

------------------------------------------------------------------------
-- Conversely, insert then delete recovers the residual key literally.

deleteInsertResidualVector :
  ∀ {n} (residual : Key.ResidualKey n) →
  Key.residualVector (Key.deleteKey (insertKey residual))
  ≡ Key.residualVector residual
deleteInsertResidualVector residual =
  Update.subtractAfterAddAt
    (Key.residualCopies residual)
    (Key.residualIndex residual)
    (Key.residualVector residual)

deleteInsertKey :
  ∀ {n} (residual : Key.ResidualKey n) →
  Key.deleteKey (insertKey residual) ≡ residual
deleteInsertKey (vector , index , predecessor , unit)
  with deleteInsertResidualVector (vector , index , predecessor , unit)
... | refl =
  cong
    (λ recoveredPredecessor → vector , index , recoveredPredecessor , unit)
    (insertedOccurrenceToNat (vector , index , predecessor , unit))

------------------------------------------------------------------------
-- The proof-free cell and residual carriers are now literally isomorphic.
------------------------------------------------------------------------
