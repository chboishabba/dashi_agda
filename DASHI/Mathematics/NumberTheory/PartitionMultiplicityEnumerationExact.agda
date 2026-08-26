module DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact where

------------------------------------------------------------------------
-- EXECUTABLE ALL-n INTEGER-PARTITION ENUMERATION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using (map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Properties using (_≟_)
import Data.Vec.Base as Vec
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.NumberTheory.PartitionMarkedUnitEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product

------------------------------------------------------------------------
-- Original executable Nat-valued box.

natsUpTo : Nat → List Nat
natsUpTo bound = map toℕ (Finite.allFin (suc bound))

prependAll :
  ∀ {dimension : Nat} →
  List Nat → List (Vec.Vec Nat dimension) →
  List (Vec.Vec Nat (suc dimension))
prependAll [] tails = []
prependAll (head ∷ heads) tails =
  map (Vec._∷_ head) tails ++ prependAll heads tails

boundedVectors :
  (dimension bound : Nat) → List (Vec.Vec Nat dimension)
boundedVectors zero bound = Vec.[] ∷ []
boundedVectors (suc dimension) bound =
  prependAll
    (natsUpTo bound)
    (boundedVectors dimension bound)

------------------------------------------------------------------------
-- Proof-oriented box, extracted from the repo's YM/NS finite-product pattern.
--
-- Keeping coordinates as Fin (bound+1) gives finite-product completeness for
-- free from FiniteProductEnumerationExact.  Mapping to Nat is postponed until
-- after the finite box is constructed.

finBoundedVectors :
  (dimension bound : Nat) →
  List (Vec.Vec (Fin (suc bound)) dimension)
finBoundedVectors dimension bound =
  Product.allFinVectorPower (suc bound) dimension

finVectorToNat :
  ∀ {dimension bound : Nat} →
  Vec.Vec (Fin (suc bound)) dimension →
  Vec.Vec Nat dimension
finVectorToNat Vec.[] = Vec.[]
finVectorToNat (head Vec.∷ tail) =
  toℕ head Vec.∷ finVectorToNat tail

proofBoundedVectors :
  (dimension bound : Nat) → List (Vec.Vec Nat dimension)
proofBoundedVectors dimension bound =
  map finVectorToNat (finBoundedVectors dimension bound)

record BoundedVectorRepresentation
    {dimension bound : Nat}
    (vector : Vec.Vec Nat dimension) : Set where
  constructor boundedVectorRepresentation
  field
    finRepresentative : Vec.Vec (Fin (suc bound)) dimension
    representativeExact : finVectorToNat finRepresentative ≡ vector

open BoundedVectorRepresentation public

representedVectorListed :
  ∀ {dimension bound : Nat}
    {vector : Vec.Vec Nat dimension} →
  BoundedVectorRepresentation {dimension} {bound} vector →
  vector ∈ proofBoundedVectors dimension bound
representedVectorListed
    (boundedVectorRepresentation representative refl) =
  Product.mapMember finVectorToNat
    (Product.allFinVectorPowerComplete representative)

------------------------------------------------------------------------
-- Proof-bearing mass filter.

packIfPartition :
  {n : Nat} →
  Vec.Vec Nat n → List (Partition.MultiplicityPartition n)
packIfPartition {n = n} vector
  with Partition.weightedMass vector ≟ n
... | yes massProof =
  Partition.multiplicityPartition vector massProof ∷ []
... | no _ = []

packCandidates :
  {n : Nat} →
  List (Vec.Vec Nat n) → List (Partition.MultiplicityPartition n)
packCandidates [] = []
packCandidates (vector ∷ vectors) =
  packIfPartition vector ++ packCandidates vectors

enumerateMultiplicityPartitions :
  (n : Nat) → List (Partition.MultiplicityPartition n)
enumerateMultiplicityPartitions n =
  packCandidates (boundedVectors n n)

proofEnumerateMultiplicityPartitions :
  (n : Nat) → List (Partition.MultiplicityPartition n)
proofEnumerateMultiplicityPartitions n =
  packCandidates (proofBoundedVectors n n)

------------------------------------------------------------------------
-- Generic finite-product completeness is now closed.  The remaining
-- partition-specific completeness step is only the elementary coordinate
-- estimate m_j <= n, used to construct BoundedVectorRepresentation for each
-- mass-n partition.  representedVectorListed then supplies box membership.
------------------------------------------------------------------------

record MultiplicityEnumerationProofBoundary : Set₁ where
  field
    everyPartitionCoordinateAtMostGrade : Set
    partitionHasBoundedVectorRepresentation : Set
    packedEnumerationComplete : Set
    proofBoundedVectorsUnique : Set
    packedEnumerationUnique : Set

------------------------------------------------------------------------
-- No Bishop/real/complex analysis is imported at this layer.
------------------------------------------------------------------------
