module DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyCardinalityExact where

------------------------------------------------------------------------
-- EXACT CARDINALITY OF THE PROOF-FREE MARKED KEY LIST
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
import Data.Nat.Properties as NatP
open import Data.Nat.Properties using (_≟_)
open import Data.Vec.Base using (Vec)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityNormalizationExact as Normalize
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionGradedPointingInstanceExact as Pointing
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Constant fold over allFin.  Multiplication is oriented with the varying
-- finite-cardinality coordinate in the second argument so recursive reduction
-- follows the list constructor.

foldConstantAllFin :
  (constant n : Nat) →
  Reindex.foldNat (λ (_ : Fin n) → constant) (Finite.allFin n)
  ≡ constant * n
foldConstantAllFin constant zero = refl
foldConstantAllFin constant (suc n) =
  cong (constant +_) (foldConstantAllFin constant n)

------------------------------------------------------------------------
-- One (occurrence,unit) fibre has m_v * v elements.

occurrenceUnitLength :
  ∀ {n} (vector : Vec Nat n) (index : Fin n) →
  Reindex.listLength (Key.occurrenceUnitEnumeration vector index)
  ≡ Partition.lookupMultiplicity index vector * Partition.partValue index
occurrenceUnitLength vector index =
  trans
    (Card.dependentPairsLength
      (Finite.allFin (Partition.lookupMultiplicity index vector))
      (λ _ → Finite.allFin (Partition.partValue index)))
    (trans
      (Reindex.foldPointwise
        (λ _ → Reindex.listLength (Finite.allFin (Partition.partValue index)))
        (λ _ → Partition.partValue index)
        (Finite.allFin (Partition.lookupMultiplicity index vector))
        (λ _ → Finite.allFinLength (Partition.partValue index)))
      (trans
        (foldConstantAllFin
          (Partition.partValue index)
          (Partition.lookupMultiplicity index vector))
        (NatP.*-comm
          (Partition.partValue index)
          (Partition.lookupMultiplicity index vector))))

------------------------------------------------------------------------
-- Sum the fibre cardinalities over part coordinates.

partValueWeightedFoldEqualsMass :
  ∀ {n} (vector : Vec Nat n) →
  Reindex.foldNat
    (λ index →
      Partition.partValue index * Partition.lookupMultiplicity index vector)
    (Finite.allFin n)
  ≡ Partition.weightedMass vector
partValueWeightedFoldEqualsMass vector =
  trans
    (Reindex.foldPointwise
      (λ index →
        Partition.partValue index * Partition.lookupMultiplicity index vector)
      (λ index →
        Partition.coordinateWeightFrom 1 index
        * Partition.lookupMultiplicity index vector)
      (Finite.allFin _)
      (λ index →
        cong
          (_* Partition.lookupMultiplicity index vector)
          (sym (Normalize.coordinateWeightOneIsPartValue index))))
    (Pointing.weightedGeneratorFoldFrom 1 vector)

partCellLength :
  ∀ {n} (vector : Vec Nat n) →
  Reindex.listLength (Key.partCellEnumeration vector)
  ≡ Partition.weightedMass vector
partCellLength {n} vector =
  trans
    (Card.dependentPairsLength
      (Finite.allFin n)
      (Key.occurrenceUnitEnumeration vector))
    (trans
      (Reindex.foldPointwise
        (λ index →
          Reindex.listLength (Key.occurrenceUnitEnumeration vector index))
        (λ index →
          Partition.lookupMultiplicity index vector * Partition.partValue index)
        (Finite.allFin n)
        (occurrenceUnitLength vector))
      (trans
        (Reindex.foldPointwise
          (λ index →
            Partition.lookupMultiplicity index vector * Partition.partValue index)
          (λ index →
            Partition.partValue index * Partition.lookupMultiplicity index vector)
          (Finite.allFin n)
          (λ index → NatP.*-comm
            (Partition.lookupMultiplicity index vector)
            (Partition.partValue index)))
        (partValueWeightedFoldEqualsMass vector)))

------------------------------------------------------------------------
-- Every vector retained by selectMass really has the selected mass.

selectMassSound :
  ∀ {n} {vector : Vec Nat n} {vectors : List (Vec Nat n)} →
  vector ∈ Enumeration.selectMass {n} vectors →
  Partition.weightedMass vector ≡ n
selectMassSound {vectors = []} ()
selectMassSound {n} {vector} {vectors = head ∷ tail} member
  with Partition.weightedMass head ≟ n
... | yes headMass with member
...   | Any.here equality =
  subst
    (λ candidate → Partition.weightedMass candidate ≡ n)
    (sym equality)
    headMass
...   | Any.there rest = selectMassSound rest
... | no _ = selectMassSound member

partitionVectorMassSound :
  ∀ {n} {vector : Vec Nat n} →
  vector ∈ Enumeration.partitionMultiplicityVectors n →
  Partition.weightedMass vector ≡ n
partitionVectorMassSound = selectMassSound

partitionVectorsAllMass :
  (n : Nat) →
  All.All (λ vector → Partition.weightedMass vector ≡ n)
    (Enumeration.partitionMultiplicityVectors n)
partitionVectorsAllMass n = All.tabulate partitionVectorMassSound

------------------------------------------------------------------------
-- A fold whose entries are all the same constant is constant * length.

foldAllEqualConstant :
  ∀ {A : Set} {constant : Nat} {xs : List A}
    (weight : A → Nat) →
  All.All (λ x → weight x ≡ constant) xs →
  Reindex.foldNat weight xs ≡ constant * Reindex.listLength xs
foldAllEqualConstant weight All.[] = refl
foldAllEqualConstant weight (All._∷_ headExact tailExact) =
  trans
    (cong₂ _+_
      headExact
      (foldAllEqualConstant weight tailExact))
    refl
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C)
    {a a' : A} {b b' : B} →
    a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ f refl refl = refl

canonicalPartitionCount : Nat → Nat
canonicalPartitionCount n =
  Reindex.listLength (Enumeration.partitionMultiplicityVectors n)

cellKeyEnumerationLength :
  (n : Nat) →
  Reindex.listLength (Key.cellKeyEnumeration n)
  ≡ n * canonicalPartitionCount n
cellKeyEnumerationLength n =
  trans
    (Card.dependentPairsLength
      (Enumeration.partitionMultiplicityVectors n)
      Key.partCellEnumeration)
    (trans
      (Reindex.foldPointwise
        (λ vector → Reindex.listLength (Key.partCellEnumeration vector))
        Partition.weightedMass
        (Enumeration.partitionMultiplicityVectors n)
        partCellLength)
      (foldAllEqualConstant
        Partition.weightedMass
        (partitionVectorsAllMass n)))

cellKeyUnitFold : (n : Nat) → Nat
cellKeyUnitFold n =
  Reindex.foldNat (λ _ → 1) (Key.cellKeyEnumeration n)

cellKeyUnitFoldIsNCount :
  (n : Nat) → cellKeyUnitFold n ≡ n * canonicalPartitionCount n
cellKeyUnitFoldIsNCount n =
  trans
    (Reindex.foldOneIsLength (Key.cellKeyEnumeration n))
    (cellKeyEnumerationLength n)

------------------------------------------------------------------------
-- This is exactly the left-hand evaluation required by ErdosDeletionFibreSystem.
------------------------------------------------------------------------
