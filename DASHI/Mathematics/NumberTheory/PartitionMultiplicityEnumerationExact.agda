module DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact where

------------------------------------------------------------------------
-- EXECUTABLE ALL-n INTEGER-PARTITION ENUMERATION
--
-- For fixed n, every multiplicity m_j of a part of size j is at most n.
-- Therefore all partitions of n occur among the finite box
--
--   {0,...,n}^n.
--
-- This owner enumerates that box and retains exactly the vectors whose weighted
-- mass is n, packaging the equality proof into MultiplicityPartition n.
-- The construction is intentionally inefficient but completely finite and is
-- suitable as a proof carrier / regression oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (map; _++_)
open import Data.Nat.Properties using (_≟_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.NumberTheory.PartitionMarkedUnitEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition

------------------------------------------------------------------------
-- Coordinates 0,...,bound.

natsUpTo : Nat → List Nat
natsUpTo bound = map toℕ (Finite.allFin (suc bound))

------------------------------------------------------------------------
-- Cartesian box {0,...,bound}^dimension.

prependAll :
  ∀ {dimension : Nat} →
  List Nat → List (Vec Nat dimension) →
  List (Vec Nat (suc dimension))
prependAll [] tails = []
prependAll (head ∷ heads) tails =
  map (head ∷_) tails ++ prependAll heads tails

boundedVectors :
  (dimension bound : Nat) → List (Vec Nat dimension)
boundedVectors zero bound = [] ∷ []
boundedVectors (suc dimension) bound =
  prependAll
    (natsUpTo bound)
    (boundedVectors dimension bound)

------------------------------------------------------------------------
-- Proof-bearing mass filter.

packIfPartition :
  {n : Nat} →
  Vec Nat n → List (Partition.MultiplicityPartition n)
packIfPartition {n = n} vector
  with Partition.weightedMass vector ≟ n
... | yes massProof =
  Partition.multiplicityPartition vector massProof ∷ []
... | no _ = []

packCandidates :
  {n : Nat} →
  List (Vec Nat n) → List (Partition.MultiplicityPartition n)
packCandidates [] = []
packCandidates (vector ∷ vectors) =
  packIfPartition vector ++ packCandidates vectors

enumerateMultiplicityPartitions :
  (n : Nat) → List (Partition.MultiplicityPartition n)
enumerateMultiplicityPartitions n =
  packCandidates (boundedVectors n n)

------------------------------------------------------------------------
-- Soundness is built into the dependent result type: every listed object
-- carries weightedMass multiplicities = n by construction.
--
-- Completeness and no-duplicates are separate structural theorems.  The only
-- genuinely nontrivial completeness lemma needed is the elementary bound
-- m_j <= n for every coordinate of a mass-n multiplicity vector.
------------------------------------------------------------------------

record MultiplicityEnumerationProofBoundary : Set₁ where
  field
    everyPartitionCoordinateAtMostGrade : Set
    boundedVectorsComplete : Set
    packedEnumerationComplete : Set
    boundedVectorsUnique : Set
    packedEnumerationUnique : Set

------------------------------------------------------------------------
-- This closes the previous absence of an all-n executable partition carrier.
-- No Bishop/real/complex analysis is imported at this layer.
------------------------------------------------------------------------
