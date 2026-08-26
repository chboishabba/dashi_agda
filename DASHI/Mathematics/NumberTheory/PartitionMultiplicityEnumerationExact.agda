module DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact where

------------------------------------------------------------------------
-- EXECUTABLE ALL-n INTEGER-PARTITION ENUMERATION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
import Data.Fin.Properties as FinP
open import Data.List.Base using (map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Nat.Base using (s≤s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Vec.Base as Vec
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; cong₂; subst)

import DASHI.Mathematics.NumberTheory.PartitionMarkedUnitEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product

------------------------------------------------------------------------
-- Original executable Nat-valued box retained as a regression oracle.

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
-- Proof-oriented unique box inherited from the repo's NS/YM finite-product
-- machinery.  Coordinates stay in Fin(bound+1) until after enumeration.

finBoundedVectors :
  (dimension bound : Nat) →
  List (Vec.Vec (Fin (suc bound)) dimension)
finBoundedVectors dimension bound =
  Product.uniqueFinVectorPower (suc bound) dimension

finVectorToNat :
  ∀ {dimension bound : Nat} →
  Vec.Vec (Fin (suc bound)) dimension →
  Vec.Vec Nat dimension
finVectorToNat Vec.[] = Vec.[]
finVectorToNat (head Vec.∷ tail) =
  toℕ head Vec.∷ finVectorToNat tail

natVecConsInjective :
  ∀ {n : Nat} {x y : Nat} {xs ys : Vec.Vec Nat n} →
  (x Vec.∷ xs) ≡ (y Vec.∷ ys) → (x ≡ y) × (xs ≡ ys)
natVecConsInjective refl = refl , refl

finVectorToNatInjective :
  ∀ {dimension bound : Nat}
    {left right : Vec.Vec (Fin (suc bound)) dimension} →
  finVectorToNat left ≡ finVectorToNat right → left ≡ right
finVectorToNatInjective {left = Vec.[]} {right = Vec.[]} equality = refl
finVectorToNatInjective
    {left = leftHead Vec.∷ leftTail}
    {right = rightHead Vec.∷ rightTail}
    equality =
  cong₂ Vec._∷_
    (FinP.toℕ-injective (proj₁ pieces))
    (finVectorToNatInjective (proj₂ pieces))
  where
  pieces :
    toℕ leftHead ≡ toℕ rightHead
      × finVectorToNat leftTail ≡ finVectorToNat rightTail
  pieces = natVecConsInjective equality

proofBoundedVectors :
  (dimension bound : Nat) → List (Vec.Vec Nat dimension)
proofBoundedVectors dimension bound =
  map finVectorToNat (finBoundedVectors dimension bound)

finBoundedVectorsUnique :
  (dimension bound : Nat) → Unique (finBoundedVectors dimension bound)
finBoundedVectorsUnique dimension bound =
  Product.uniqueFinVectorPowerNoDuplicates (suc bound) dimension

proofBoundedVectorsUnique :
  (dimension bound : Nat) → Unique (proofBoundedVectors dimension bound)
proofBoundedVectorsUnique dimension bound =
  UniqueP.map⁺ finVectorToNatInjective
    (finBoundedVectorsUnique dimension bound)

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
    (Product.uniqueFinVectorPowerComplete representative)

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
      (FinP.toℕ-fromℕ< (s≤s (bounds Data.Fin.Base.zero)))
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
-- Canonical unique partition DATA enumeration.
--
-- Counting uses multiplicity vectors, not equality of proof records.  The mass
-- predicate is decidable, and selecting from a unique finite box preserves
-- uniqueness literally.

selectMass :
  {n : Nat} →
  List (Vec.Vec Nat n) → List (Vec.Vec Nat n)
selectMass {n} [] = []
selectMass {n} (vector ∷ vectors)
  with Partition.weightedMass vector ≟ n
... | yes _ = vector ∷ selectMass vectors
... | no _ = selectMass vectors

selectedMassMemberOriginal :
  ∀ {n : Nat} {vector : Vec.Vec Nat n} {vectors} →
  vector ∈ selectMass {n} vectors → vector ∈ vectors
selectedMassMemberOriginal {vectors = []} ()
selectedMassMemberOriginal {n} {vectors = head ∷ tail} member
  with Partition.weightedMass head ≟ n
... | yes _ with member
...   | Any.here equality = Any.here equality
...   | Any.there rest = Any.there (selectedMassMemberOriginal rest)
... | no _ = Any.there (selectedMassMemberOriginal member)

selectMassUnique :
  ∀ {n : Nat} {vectors : List (Vec.Vec Nat n)} →
  Unique vectors → Unique (selectMass {n} vectors)
selectMassUnique {vectors = []} AllPairs.[] = AllPairs.[]
selectMassUnique {n} {vectors = head ∷ tail}
    (AllPairs._∷_ fresh rest)
  with Partition.weightedMass head ≟ n
... | yes _ =
  AllPairs._∷_
    selectedFresh
    (selectMassUnique rest)
  where
  selectedFresh :
    All.All (λ other → head ≢ other) (selectMass {n} tail)
  selectedFresh =
    All.tabulate
      (λ member →
        All.lookup fresh (selectedMassMemberOriginal member))
... | no _ = selectMassUnique rest

partitionMultiplicityVectors :
  (n : Nat) → List (Vec.Vec Nat n)
partitionMultiplicityVectors n =
  selectMass (proofBoundedVectors n n)

partitionMultiplicityVectorsUnique :
  (n : Nat) → Unique (partitionMultiplicityVectors n)
partitionMultiplicityVectorsUnique n =
  selectMassUnique (proofBoundedVectorsUnique n n)

selectMassComplete :
  ∀ {n : Nat}
    {vector : Vec.Vec Nat n} {vectors : List (Vec.Vec Nat n)} →
  vector ∈ vectors →
  Partition.weightedMass vector ≡ n →
  vector ∈ selectMass {n} vectors
selectMassComplete {vectors = []} () massProof
selectMassComplete {n} {vector} {vectors = head ∷ tail}
    (Any.here equality) massProof
  with Partition.weightedMass head ≟ n
... | yes _ = Any.here equality
... | no contradiction =
  ⊥-elim
    (contradiction
      (subst
        (λ candidate → Partition.weightedMass candidate ≡ n)
        equality massProof))
selectMassComplete {n} {vector} {vectors = head ∷ tail}
    (Any.there member) massProof
  with Partition.weightedMass head ≟ n
... | yes _ = Any.there (selectMassComplete member massProof)
... | no _ = selectMassComplete member massProof

partitionMultiplicityVectorComplete :
  ∀ {n : Nat}
    (partition : Partition.MultiplicityPartition n) →
  Partition.multiplicities partition ∈ partitionMultiplicityVectors n
partitionMultiplicityVectorComplete partition =
  selectMassComplete
    (partitionCandidateListed partition)
    (Partition.massExact partition)

------------------------------------------------------------------------
-- The canonical counting carrier is now finite, complete and duplicate-free.
-- Proof-bearing MultiplicityPartition values are reconstructed only at theorem
-- consumption sites, avoiding any need for equality of mass proofs.
--
-- No Bishop/real/complex analysis is imported at this layer.
------------------------------------------------------------------------
