module DASHI.Physics.Closure.NSTriadKNCanonicalOrbitFoldEquality where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Bool.Base using (not)
open import Data.List.Base using (List; []; _∷_; filterᵇ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumeration as Orbit
import DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumerationConcrete as Concrete
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Exact finite regrouping.
--
-- `canonicalFoldBy` selects the first remaining representative and folds all
-- later members of its decidable orbit into that representative before moving
-- to the complement.  The theorem below proves that this regrouping changes
-- neither the ordered finite sum nor its scalar value.
------------------------------------------------------------------------

sumBy :
  {A : Set} → (S : Scalar.ExactOrderedScalar) →
  (A → Scalar.Scalar S) → List A → Scalar.Scalar S
sumBy S f [] = Scalar.zero S
sumBy S f (x ∷ xs) = Scalar._+_ S (f x) (sumBy S f xs)

relatedTail :
  {A : Set} → (same? : A → A → Bool) → A → List A → List A
relatedTail same? pivot = filterᵇ (λ x → same? x pivot)

unrelatedTail :
  {A : Set} → (same? : A → A → Bool) → A → List A → List A
unrelatedTail same? pivot = filterᵇ (λ x → not (same? x pivot))

canonicalFoldBy :
  {A : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (same? : A → A → Bool) →
  (A → Scalar.Scalar (Algebra.orderedScalar K)) →
  List A → Scalar.Scalar (Algebra.orderedScalar K)
canonicalFoldBy K same? f [] = Scalar.zero (Algebra.orderedScalar K)
canonicalFoldBy K same? f (pivot ∷ xs) =
  Scalar._+_ S
    (Scalar._+_ S (f pivot)
      (sumBy S f (relatedTail same? pivot xs)))
    (canonicalFoldBy K same? f (unrelatedTail same? pivot xs))
  where
  S = Algebra.orderedScalar K

filterPartitionSum :
  {A : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (same? : A → A → Bool) →
  (f : A → Scalar.Scalar (Algebra.orderedScalar K)) →
  (pivot : A) → (xs : List A) →
  Scalar._+_ (Algebra.orderedScalar K)
    (sumBy (Algebra.orderedScalar K) f (relatedTail same? pivot xs))
    (sumBy (Algebra.orderedScalar K) f (unrelatedTail same? pivot xs)) ≡
  sumBy (Algebra.orderedScalar K) f xs
filterPartitionSum K same? f pivot [] =
  Algebra.addZeroLeft K (Scalar.zero (Algebra.orderedScalar K))
filterPartitionSum K same? f pivot (x ∷ xs) with same? x pivot
... | true =
  trans
    (Algebra.addAssociative K (f x)
      (sumBy S f (relatedTail same? pivot xs))
      (sumBy S f (unrelatedTail same? pivot xs)))
    (cong (Scalar._+_ S (f x))
      (filterPartitionSum K same? f pivot xs))
  where
  S = Algebra.orderedScalar K
... | false =
  trans
    (symAssoc
      (sumBy S f (relatedTail same? pivot xs))
      (f x)
      (sumBy S f (unrelatedTail same? pivot xs)))
    (trans
      (cong
        (λ q → Scalar._+_ S q
          (sumBy S f (unrelatedTail same? pivot xs)))
        (Algebra.addCommutative K
          (sumBy S f (relatedTail same? pivot xs)) (f x)))
      (trans
        (Algebra.addAssociative K (f x)
          (sumBy S f (relatedTail same? pivot xs))
          (sumBy S f (unrelatedTail same? pivot xs)))
        (cong (Scalar._+_ S (f x))
          (filterPartitionSum K same? f pivot xs))))
  where
  S = Algebra.orderedScalar K

  symAssoc :
    (a b c : Scalar.Scalar S) →
    Scalar._+_ S a (Scalar._+_ S b c) ≡
    Scalar._+_ S (Scalar._+_ S a b) c
  symAssoc a b c = sym (Algebra.addAssociative K a b c)

canonicalFoldByEqualsOrderedFold :
  {A : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (same? : A → A → Bool) →
  (f : A → Scalar.Scalar (Algebra.orderedScalar K)) →
  (xs : List A) →
  canonicalFoldBy K same? f xs ≡
  sumBy (Algebra.orderedScalar K) f xs
canonicalFoldByEqualsOrderedFold K same? f [] = refl
canonicalFoldByEqualsOrderedFold K same? f (pivot ∷ xs) =
  trans
    (cong (Scalar._+_ S block)
      (canonicalFoldByEqualsOrderedFold K same? f
        (unrelatedTail same? pivot xs)))
    (trans
      (Algebra.addAssociative K (f pivot) related unrelated)
      (cong (Scalar._+_ S (f pivot))
        (filterPartitionSum K same? f pivot xs)))
  where
  S = Algebra.orderedScalar K
  related = sumBy S f (relatedTail same? pivot xs)
  unrelated = sumBy S f (unrelatedTail same? pivot xs)
  block = Scalar._+_ S (f pivot) related

------------------------------------------------------------------------
-- Full-cutoff zero-sum witness list and the concrete Galerkin specialization.
------------------------------------------------------------------------

fullCutoffZeroSumWitnesses : Nat → List Energy.ZeroSumTriad
fullCutoffZeroSumWitnesses R =
  Concrete.attachRepresentatives R (Orbit.fullCutoffZeroSumTriads R)
    (Orbit.fullCutoffZeroSumTriadsSound R)

sameZeroSumOrbit? : Energy.ZeroSumTriad → Energy.ZeroSumTriad → Bool
sameZeroSumOrbit? σ ρ =
  Concrete.sameOrbit? (Energy.triad σ) (Energy.triad ρ)

orderedGalerkinPacketTransferSum :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
orderedGalerkinPacketTransferSum K M R z T =
  sumBy S (Energy.weightedZeroSumTriadContribution S M z T)
    (fullCutoffZeroSumWitnesses R)
  where
  S = Algebra.orderedScalar K

canonicalRegroupedPacketTransferSum :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalRegroupedPacketTransferSum K M R z T =
  canonicalFoldBy K sameZeroSumOrbit?
    (Energy.weightedZeroSumTriadContribution S M z T)
    (fullCutoffZeroSumWitnesses R)
  where
  S = Algebra.orderedScalar K

canonicalRegroupedEqualsOrderedGalerkin :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  (z : Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (T : Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  canonicalRegroupedPacketTransferSum K M R z T ≡
  orderedGalerkinPacketTransferSum K M R z T
canonicalRegroupedEqualsOrderedGalerkin K M R z T =
  canonicalFoldByEqualsOrderedFold K sameZeroSumOrbit?
    (Energy.weightedZeroSumTriadContribution (Algebra.orderedScalar K) M z T)
    (fullCutoffZeroSumWitnesses R)
