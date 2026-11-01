module DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeySystemExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- STRICT FINITE SYSTEM
--
-- Instantiate the pre-existing ErdosDeletionFibreSystem using proof-free cell
-- and residual keys.  The residual list is literally the mapped deletion image
-- of the unique cell list, so the generic permutation/fold theorem applies
-- without equality of partition proof records.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP

import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteDoubleCountBridgeExact as Bridge
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyCardinalityExact as Cardinality
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyRoundTripExact as RoundTrip

residualKeyEnumeration :
  (n : Nat) → List (Key.ResidualKey n)
residualKeyEnumeration n =
  map Key.deleteKey (Key.cellKeyEnumeration n)

residualKeyEnumerationUnique :
  (n : Nat) → Unique (residualKeyEnumeration n)
residualKeyEnumerationUnique n =
  UniqueP.map⁺ RoundTrip.deleteKeyInjective
    (Key.cellKeyEnumerationUnique n)

markedWeight : ∀ {n} → Key.CellKey n → Nat
markedWeight _ = 1

residualWeight : ∀ {n} → Key.ResidualKey n → Nat
residualWeight _ = 1

canonicalErdosFiniteKeySystem : Bridge.ErdosDeletionFibreSystem
canonicalErdosFiniteKeySystem = record
  { PartitionCount = Cardinality.canonicalPartitionCount
  ; Marked = Key.CellKey
  ; Residual = Key.ResidualKey
  ; markedEnumeration = Key.cellKeyEnumeration
  ; residualEnumeration = residualKeyEnumeration
  ; delete = Key.deleteKey
  ; markedWeight = markedWeight
  ; residualWeight = residualWeight
  ; markedUnique = Key.cellKeyEnumerationUnique
  ; residualUnique = residualKeyEnumerationUnique
  ; deleteInjective = RoundTrip.deleteKeyInjective
  ; mappedDeleteForward = λ member → member
  ; mappedDeleteBackward = λ member → member
  ; deletePreservesWeight = λ _ → refl
  ; markedFoldEvaluation = Cardinality.cellKeyUnitFoldIsNCount
  }

------------------------------------------------------------------------
-- The arbitrary-n finite double-count theorem is now a direct specialization
-- of the generic bridge.

canonicalErdosKeyIdentity :
  (n : Nat) →
  n * Cardinality.canonicalPartitionCount n
  ≡ Bridge.ErdosResidualDoubleSum canonicalErdosFiniteKeySystem n
canonicalErdosKeyIdentity =
  Bridge.erdosIdentityFromDeletionFibre canonicalErdosFiniteKeySystem

------------------------------------------------------------------------
-- The RHS here is the literal unit-labelled deletion image.  Identifying that
-- image with the conventional (v,k,mu,u) / factor-pair enumeration is the next
-- grouping theorem, not an assumption of this system.
------------------------------------------------------------------------
