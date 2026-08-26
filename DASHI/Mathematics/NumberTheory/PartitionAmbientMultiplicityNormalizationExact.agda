module DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityNormalizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- PURPOSE
-- Close the representation boundary created by literal deletion.  A residual
-- produced from a grade-n partition retains an ambient Vec Nat n while its
-- exact mass is r=n-kv.  Since every coordinate whose part weight exceeds r
-- is zero, the ambient vector canonically truncates to its first r coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteVectorPrefixSplitExact as Split
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityDeletionExact as Ambient

------------------------------------------------------------------------
-- Agreement of the neutral vector lookup with the partition lookup.

lookupAgreement :
  ∀ {n : Nat} (index : Fin n) (vector : Vec Nat n) →
  Split.lookupVec index vector ≡ Partition.lookupMultiplicity index vector
lookupAgreement fzero (x Data.Vec.Base.∷ xs) = refl
lookupAgreement (fsuc index) (x Data.Vec.Base.∷ xs) =
  lookupAgreement index xs

------------------------------------------------------------------------
-- Recursive coordinate weight agrees with the familiar part value 1+index.

coordinateWeightFromSuc :
  ∀ {n : Nat} (first : Nat) (index : Fin n) →
  Partition.coordinateWeightFrom (suc first) index
  ≡ suc (Partition.coordinateWeightFrom first index)
coordinateWeightFromSuc first fzero = refl
coordinateWeightFromSuc first (fsuc index) =
  coordinateWeightFromSuc (suc first) index

coordinateWeightOneIsPartValue :
  ∀ {n : Nat} (index : Fin n) →
  Partition.coordinateWeightFrom 1 index ≡ Partition.partValue index
coordinateWeightOneIsPartValue fzero = refl
coordinateWeightOneIsPartValue (fsuc index) =
  trans
    (coordinateWeightFromSuc 1 index)
    (cong suc (coordinateWeightOneIsPartValue index))

tailCoordinateWeightAbovePrefix :
  ∀ {tail : Nat}
    (prefix : Nat) (index : Fin tail) →
  prefix <
    Partition.coordinateWeightFrom 1 (Split.shiftIndexBy prefix index)
tailCoordinateWeightAbovePrefix prefix index =
  subst
    (λ weight → prefix < weight)
    (sym weightExact)
    (Split.prefixLessThanShiftedSuccessor prefix (toℕ index))
  where
  weightExact :
    Partition.coordinateWeightFrom 1 (Split.shiftIndexBy prefix index)
    ≡ suc (prefix + toℕ index)
  weightExact =
    trans
      (coordinateWeightOneIsPartValue (Split.shiftIndexBy prefix index))
      (cong suc (Split.shiftIndexToNat prefix index))

------------------------------------------------------------------------
-- Exact weighted-mass split across a vector prefix.

advanceWeight : Nat → Nat → Nat
advanceWeight first zero = first
advanceWeight first (suc prefix) = advanceWeight (suc first) prefix

weightedMassFromSplit :
  ∀ {tail : Nat}
    (first prefix : Nat)
    (vector : Vec Nat (prefix + tail)) →
  Partition.weightedMassFrom first vector
  ≡
  Partition.weightedMassFrom first (Split.takePrefix prefix tail vector)
  + Partition.weightedMassFrom (advanceWeight first prefix)
      (Split.dropPrefix prefix tail vector)
weightedMassFromSplit first zero vector = refl
weightedMassFromSplit first (suc prefix) (x Data.Vec.Base.∷ xs) =
  trans
    (cong
      (first * x +_)
      (weightedMassFromSplit (suc first) prefix xs))
    (sym
      (NatP.+-assoc
        (first * x)
        (Partition.weightedMassFrom (suc first)
          (Split.takePrefix prefix _ xs))
        (Partition.weightedMassFrom (advanceWeight (suc first) prefix)
          (Split.dropPrefix prefix _ xs))))

weightedMassFromZeroVec :
  (first dimension : Nat) →
  Partition.weightedMassFrom first (Split.zeroVec dimension) ≡ zero
weightedMassFromZeroVec first zero = refl
weightedMassFromZeroVec first (suc dimension) =
  trans
    (cong
      (first * zero +_)
      (weightedMassFromZeroVec (suc first) dimension))
    refl

------------------------------------------------------------------------
-- Every exact-mass-r ambient vector of dimension r+extra has a zero tail.

ambientTailPointwiseZero :
  ∀ {mass extra : Nat}
    (ambient : Ambient.AmbientMultiplicityPartition (mass + extra) mass)
    (index : Fin extra) →
  Split.lookupVec index
    (Split.dropPrefix mass extra (Ambient.ambientMultiplicities ambient))
  ≡ zero
ambientTailPointwiseZero {mass} {extra} ambient index =
  trans
    (Split.lookupDropPrefix mass index (Ambient.ambientMultiplicities ambient))
    (trans
      (lookupAgreement
        (Split.shiftIndexBy mass index)
        (Ambient.ambientMultiplicities ambient))
      (Partition.coordinateAboveExactMassIsZero
        (Ambient.ambientMultiplicities ambient)
        (Ambient.ambientMassExact ambient)
        (Split.shiftIndexBy mass index)
        (tailCoordinateWeightAbovePrefix mass index)))

ambientTailZero :
  ∀ {mass extra : Nat}
    (ambient : Ambient.AmbientMultiplicityPartition (mass + extra) mass) →
  Split.dropPrefix mass extra (Ambient.ambientMultiplicities ambient)
  ≡ Split.zeroVec extra
ambientTailZero ambient =
  Split.pointwiseZeroToVectorZero _ (ambientTailPointwiseZero ambient)

------------------------------------------------------------------------
-- Therefore the retained prefix has exact mass r and is the canonical
-- MultiplicityPartition r.

ambientPrefixMassExact :
  ∀ {mass extra : Nat}
    (ambient : Ambient.AmbientMultiplicityPartition (mass + extra) mass) →
  Partition.weightedMass
    (Split.takePrefix mass extra (Ambient.ambientMultiplicities ambient))
  ≡ mass
ambientPrefixMassExact {mass} {extra} ambient =
  trans
    (sym totalEqualsPrefix)
    (Ambient.ambientMassExact ambient)
  where
  prefixVector : Vec Nat mass
  prefixVector =
    Split.takePrefix mass extra (Ambient.ambientMultiplicities ambient)

  tailVector : Vec Nat extra
  tailVector =
    Split.dropPrefix mass extra (Ambient.ambientMultiplicities ambient)

  tailMassZero :
    Partition.weightedMassFrom (advanceWeight 1 mass) tailVector ≡ zero
  tailMassZero =
    trans
      (cong
        (Partition.weightedMassFrom (advanceWeight 1 mass))
        (ambientTailZero ambient))
      (weightedMassFromZeroVec (advanceWeight 1 mass) extra)

  totalEqualsPrefix :
    Partition.weightedMass (Ambient.ambientMultiplicities ambient)
    ≡ Partition.weightedMass prefixVector
  totalEqualsPrefix =
    trans
      (weightedMassFromSplit 1 mass (Ambient.ambientMultiplicities ambient))
      (trans
        (cong (Partition.weightedMass prefixVector +_) tailMassZero)
        (NatP.+-identityʳ (Partition.weightedMass prefixVector)))

normalizeAmbient :
  ∀ {mass extra : Nat} →
  Ambient.AmbientMultiplicityPartition (mass + extra) mass →
  Partition.MultiplicityPartition mass
normalizeAmbient ambient =
  Partition.multiplicityPartition
    (Split.takePrefix _ _ (Ambient.ambientMultiplicities ambient))
    (ambientPrefixMassExact ambient)

------------------------------------------------------------------------
-- Transport an Erdős ambient residual along r+kv=n, normalize it, and recover
-- the canonical residual carrier used by p(r).

transportVectorToDecomposition :
  ∀ {left right : Nat} →
  left ≡ right → Vec Nat right → Vec Nat left
transportVectorToDecomposition refl vector = vector

transportWeightedMass :
  ∀ {left right : Nat}
    (equality : left ≡ right)
    (vector : Vec Nat right) →
  Partition.weightedMass (transportVectorToDecomposition equality vector)
  ≡ Partition.weightedMass vector
transportWeightedMass refl vector = refl

ambientResidualInDecomposedDimension :
  ∀ {n : Nat}
    (residual : Ambient.ErdosAmbientResidual n) →
  Ambient.AmbientMultiplicityPartition
    (Ambient.residualMass residual
      + Ambient.copies residual * Partition.partValue (Ambient.partIndex residual))
    (Ambient.residualMass residual)
ambientResidualInDecomposedDimension residual =
  Ambient.ambientMultiplicityPartition
    transported
    (trans
      (transportWeightedMass (Ambient.decompositionExact residual)
        (Ambient.ambientMultiplicities (Ambient.residualPartition residual)))
      (Ambient.ambientMassExact (Ambient.residualPartition residual)))
  where
  transported :
    Vec Nat
      (Ambient.residualMass residual
        + Ambient.copies residual * Partition.partValue (Ambient.partIndex residual))
  transported =
    transportVectorToDecomposition
      (Ambient.decompositionExact residual)
      (Ambient.ambientMultiplicities (Ambient.residualPartition residual))

canonicalResidualPartition :
  ∀ {n : Nat}
    (residual : Ambient.ErdosAmbientResidual n) →
  Partition.MultiplicityPartition (Ambient.residualMass residual)
canonicalResidualPartition residual =
  normalizeAmbient (ambientResidualInDecomposedDimension residual)

ambientResidualToCanonical :
  ∀ {n : Nat} →
  Ambient.ErdosAmbientResidual n → Partition.ErdosMultiplicityResidual n
ambientResidualToCanonical residual =
  Partition.erdosMultiplicityResidual
    (Ambient.partIndex residual)
    (Ambient.copies residual)
    (Ambient.copiesPositive residual)
    (Ambient.residualMass residual)
    (canonicalResidualPartition residual)
    (Ambient.decompositionExact residual)
    (Ambient.unit residual)

------------------------------------------------------------------------
-- The ambient/canonical representation boundary is now a theorem, not a cast.
------------------------------------------------------------------------
