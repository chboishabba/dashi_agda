module DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact where

------------------------------------------------------------------------
-- EXECUTABLE ALL-n INTEGER-PARTITION ENUMERATION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.List.Base using (map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using ()
open import Data.Nat.Base using (s≤s)
open import Data.Nat.Properties using (_≟_)
import Data.Vec.Base as Vec
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong₂; subst)

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
-- Any pointwise-bounded Nat vector has a canonical Fin(bound+1) lift.

boundedRepresentationFromPointwise :
  ∀ {dimension bound : Nat}
    (vector : Vec.Vec Nat dimension) →
  (∀ index → Partition.lookupMultiplicity index vector ≤ bound) →
  BoundedVectorRepresentation {dimension} {bound} vector
boundedRepresentationFromPointwise Vec.[] bounds =
  boundedVectorRepresentation Vec.[] refl
boundedRepresentationFromPointwise
    {bound = bound} (head Vec.∷ tail) bounds
  with boundedRepresentationFromPointwise tail
    (λ index → bounds (Data.Fin.Base.suc index))
... | boundedVectorRepresentation tailRepresentative tailExact =
  boundedVectorRepresentation
    (fromℕ< (s≤s (bounds Data.Fin.Base.zero)) Vec.∷ tailRepresentative)
    (cong₂ Vec._∷_
      (toℕ-fromℕ< (s≤s (bounds Data.Fin.Base.zero)))
      tailExact)

partitionBoundedVectorRepresentation :
  ∀ {n : Nat} →
  (partition : Partition.MultiplicityPartition n) →
  BoundedVectorRepresentation
    {dimension = n} {bound = n}
    (Partition.multiplicities partition)
partitionBoundedVectorRepresentation partition =
  boundedRepresentationFromPointwise
    (Partition.multiplicities partition)
    (Partition.partitionCoordinateAtMostGrade partition)

partitionCandidateListed :
  ∀ {n : Nat}
    (partition : Partition.MultiplicityPartition n) →
  Partition.multiplicities partition ∈ proofBoundedVectors n n
partitionCandidateListed partition =
  representedVectorListed (partitionBoundedVectorRepresentation partition)

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
-- Extensional completeness avoids requiring proof-irrelevance for massExact.
-- The enumerator produces a representative with the same multiplicity vector;
-- that is the mathematically relevant partition datum.

record PackedCandidateHit
    {n : Nat}
    (vector : Vec.Vec Nat n)
    (candidates : List (Vec.Vec Nat n)) : Set where
  constructor packedCandidateHit
  field
    representative : Partition.MultiplicityPartition n
    representativeListed : representative ∈ packCandidates candidates
    sameMultiplicities : Partition.multiplicities representative ≡ vector

open PackedCandidateHit public

packCandidatesCompleteVector :
  ∀ {n : Nat}
    {vector : Vec.Vec Nat n}
    {candidates : List (Vec.Vec Nat n)} →
  vector ∈ candidates →
  Partition.weightedMass vector ≡ n →
  PackedCandidateHit vector candidates
packCandidatesCompleteVector {candidates = []} () massProof
packCandidatesCompleteVector
    {n = n} {vector = vector} {candidates = head ∷ tails}
    (Any.here equality) massProof
  with Partition.weightedMass head ≟ n
... | yes headMass =
  packedCandidateHit
    (Partition.multiplicityPartition head headMass)
    (Any.here refl)
    equality
... | no headNotMass =
  ⊥-elim
    (headNotMass
      (subst
        (λ candidate → Partition.weightedMass candidate ≡ n)
        equality
        massProof))
packCandidatesCompleteVector
    {n = n} {vector = vector} {candidates = head ∷ tails}
    (Any.there member) massProof
  with Partition.weightedMass head ≟ n
... | yes headMass
  with packCandidatesCompleteVector member massProof
... | packedCandidateHit representative listed same =
  packedCandidateHit representative (Any.there listed) same
... | no headNotMass =
  packCandidatesCompleteVector member massProof

record MultiplicityPartitionEnumerationHit
    {n : Nat}
    (partition : Partition.MultiplicityPartition n) : Set where
  constructor multiplicityPartitionEnumerationHit
  field
    representative : Partition.MultiplicityPartition n
    representativeListed : representative ∈ proofEnumerateMultiplicityPartitions n
    sameMultiplicities :
      Partition.multiplicities representative
      ≡ Partition.multiplicities partition

open MultiplicityPartitionEnumerationHit public

proofMultiplicityEnumerationComplete :
  ∀ {n : Nat}
    (partition : Partition.MultiplicityPartition n) →
  MultiplicityPartitionEnumerationHit partition
proofMultiplicityEnumerationComplete partition
  with packCandidatesCompleteVector
    (partitionCandidateListed partition)
    (Partition.massExact partition)
... | packedCandidateHit representative listed same =
  multiplicityPartitionEnumerationHit representative listed same

------------------------------------------------------------------------
-- Completeness of the proof-oriented enumeration is now closed extensionally.
-- Remaining finite work is uniqueness/no-duplicates of the canonical box and
-- then the exact coordinate deletion/reconstruction bijection.
------------------------------------------------------------------------

record MultiplicityEnumerationProofBoundary : Set₁ where
  field
    proofBoundedVectorsUnique : Set
    packedEnumerationUnique : Set

------------------------------------------------------------------------
-- No Bishop/real/complex analysis is imported at this layer.
------------------------------------------------------------------------
