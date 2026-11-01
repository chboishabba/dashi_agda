module DASHI.Mathematics.NumberTheory.PartitionMultiplicityDeletionMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- PURPOSE
-- Adding/deleting k copies of the part at coordinate v changes weighted
-- partition mass by exactly k*v.  The proof is over the literal finite
-- multiplicity-vector carrier and reuses the neutral coordinate-update owner.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (_≤_; _∸_)
open import Data.Nat.Properties using
  (+-assoc; +-comm; *-comm; *-distribˡ-+; m∸n+n≡m)
open import Data.Vec.Base using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteNatVectorCoordinateUpdateExact as Update
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition

------------------------------------------------------------------------
-- Recursive coordinate weight aligned definitionally with weightedMassFrom.

coordinateWeightFrom :
  ∀ {n : Nat} → Nat → Fin n → Nat
coordinateWeightFrom first fzero = first
coordinateWeightFrom first (fsuc index) =
  coordinateWeightFrom (suc first) index

coordinateWeightFromSuc :
  ∀ {n : Nat}
    (first : Nat) (index : Fin n) →
  coordinateWeightFrom (suc first) index
  ≡ suc (coordinateWeightFrom first index)
coordinateWeightFromSuc first fzero = refl
coordinateWeightFromSuc first (fsuc index) =
  coordinateWeightFromSuc (suc first) index

coordinateWeightFromOneIsPartValue :
  ∀ {n : Nat} (index : Fin n) →
  coordinateWeightFrom 1 index ≡ Partition.partValue index
coordinateWeightFromOneIsPartValue fzero = refl
coordinateWeightFromOneIsPartValue (fsuc index) =
  trans
    (coordinateWeightFromSuc 1 index)
    (cong suc (coordinateWeightFromOneIsPartValue index))

------------------------------------------------------------------------
-- Head-coordinate arithmetic.

headDeletionMass :
  (first multiplicity amount tailMass : Nat) →
  amount ≤ multiplicity →
  (first * (multiplicity ∸ amount) + tailMass)
    + amount * first
  ≡ first * multiplicity + tailMass
headDeletionMass first multiplicity amount tailMass available =
  trans
    (+-assoc
      (first * (multiplicity ∸ amount))
      tailMass
      (amount * first))
    (trans
      (cong
        (first * (multiplicity ∸ amount) +_)
        (+-comm tailMass (amount * first)))
      (trans
        (sym
          (+-assoc
            (first * (multiplicity ∸ amount))
            (amount * first)
            tailMass))
        (cong
          (_+ tailMass)
          (trans
            (cong
              (first * (multiplicity ∸ amount) +_)
              (*-comm amount first))
            (trans
              (sym
                (*-distribˡ-+
                  first
                  (multiplicity ∸ amount)
                  amount))
              (cong (first *_) (m∸n+n≡m available)))))))

headInsertionMass :
  (first multiplicity amount tailMass : Nat) →
  first * (multiplicity + amount) + tailMass
  ≡ (first * multiplicity + tailMass) + amount * first
headInsertionMass first multiplicity amount tailMass =
  trans
    (cong (_+ tailMass)
      (*-distribˡ-+ first multiplicity amount))
    (trans
      (+-assoc (first * multiplicity) (first * amount) tailMass)
      (trans
        (cong
          (first * multiplicity +_)
          (+-comm (first * amount) tailMass))
        (trans
          (sym
            (+-assoc
              (first * multiplicity)
              tailMass
              (first * amount)))
          (cong
            ((first * multiplicity + tailMass) +_)
            (*-comm first amount)))))

------------------------------------------------------------------------
-- General deletion / insertion mass theorems.

weightedMassFromSubtractAt :
  ∀ {n : Nat}
    (first amount : Nat)
    (index : Fin n)
    (vector : Vec Nat n) →
  amount ≤ Update.lookupNat index vector →
  Partition.weightedMassFrom first
      (Update.subtractAt amount index vector)
    + amount * coordinateWeightFrom first index
  ≡ Partition.weightedMassFrom first vector
weightedMassFromSubtractAt first amount fzero
    (multiplicity ∷ rest) available =
  headDeletionMass
    first multiplicity amount
    (Partition.weightedMassFrom (suc first) rest)
    available
weightedMassFromSubtractAt first amount (fsuc index)
    (multiplicity ∷ rest) available =
  trans
    (+-assoc
      (first * multiplicity)
      (Partition.weightedMassFrom (suc first)
        (Update.subtractAt amount index rest))
      (amount * coordinateWeightFrom (suc first) index))
    (cong
      (first * multiplicity +_)
      (weightedMassFromSubtractAt
        (suc first) amount index rest available))

weightedMassFromAddAt :
  ∀ {n : Nat}
    (first amount : Nat)
    (index : Fin n)
    (vector : Vec Nat n) →
  Partition.weightedMassFrom first
      (Update.addAt amount index vector)
  ≡ Partition.weightedMassFrom first vector
      + amount * coordinateWeightFrom first index
weightedMassFromAddAt first amount fzero (multiplicity ∷ rest) =
  headInsertionMass
    first multiplicity amount
    (Partition.weightedMassFrom (suc first) rest)
weightedMassFromAddAt first amount (fsuc index) (multiplicity ∷ rest) =
  trans
    (cong
      (first * multiplicity +_)
      (weightedMassFromAddAt
        (suc first) amount index rest))
    (sym
      (+-assoc
        (first * multiplicity)
        (Partition.weightedMassFrom (suc first) rest)
        (amount * coordinateWeightFrom (suc first) index)))

------------------------------------------------------------------------
-- Partition-grade specializations.

partitionDeletionMass :
  ∀ {n : Nat}
    (partition : Partition.MultiplicityPartition n)
    (amount : Nat)
    (index : Fin n) →
  amount ≤
    Partition.lookupMultiplicity index (Partition.multiplicities partition) →
  Partition.weightedMass
      (Update.subtractAt amount index (Partition.multiplicities partition))
    + amount * Partition.partValue index
  ≡ n
partitionDeletionMass partition amount index available =
  trans
    (cong
      (λ weight →
        Partition.weightedMass
          (Update.subtractAt amount index (Partition.multiplicities partition))
        + amount * weight)
      (sym (coordinateWeightFromOneIsPartValue index)))
    (trans
      (weightedMassFromSubtractAt
        1 amount index (Partition.multiplicities partition) available)
      (Partition.massExact partition))

partitionInsertionMass :
  ∀ {n : Nat}
    (vector : Vec Nat n)
    (amount : Nat)
    (index : Fin n) →
  Partition.weightedMass (Update.addAt amount index vector)
  ≡ Partition.weightedMass vector + amount * Partition.partValue index
partitionInsertionMass vector amount index =
  trans
    (weightedMassFromAddAt 1 amount index vector)
    (cong
      (λ weight → Partition.weightedMass vector + amount * weight)
      (coordinateWeightFromOneIsPartValue index))

------------------------------------------------------------------------
-- No real/complex analysis enters these theorems.
------------------------------------------------------------------------
