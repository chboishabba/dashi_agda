module DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualCardinalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- Evaluate the conventional r=k*v residual enumeration.  Each factor pair
-- contributes v units for each partition of n-r, hence v*p(n-r); summing the
-- r-blocks gives exactly the existing factorPairGroupedRHS definition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (_++_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Positive
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionDivisorSumRegroupingExact as Regroup
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualEnumerationExact as Classical
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Generic finite fold helpers.

foldConstantLength :
  ∀ {A : Set} (constant : Nat) (xs : List A) →
  Reindex.foldNat (λ _ → constant) xs
  ≡ constant * Reindex.listLength xs
foldConstantLength constant [] = refl
foldConstantLength constant (_ ∷ xs) =
  cong (constant +_) (foldConstantLength constant xs)

foldScaledRight :
  ∀ {A : Set}
    (weight : A → Nat) (constant : Nat) (xs : List A) →
  Reindex.foldNat (λ x → weight x * constant) xs
  ≡ Reindex.foldNat weight xs * constant
foldScaledRight weight constant [] = refl
foldScaledRight weight constant (x ∷ xs) =
  trans
    (cong (weight x * constant +_)
      (foldScaledRight weight constant xs))
    (sym (rightDistribute (weight x) (Reindex.foldNat weight xs) constant))
  where
  rightDistribute :
    (left right factor : Nat) →
    (left + right) * factor ≡ left * factor + right * factor
  rightDistribute left right factor =
    trans
      (NatP.*-comm (left + right) factor)
      (trans
        (NatP.*-distribˡ-+ factor left right)
        (cong₂ _+_
          (NatP.*-comm factor left)
          (NatP.*-comm factor right)))
    where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {a a' : A} {b b' : B} →
      a ≡ a' → b ≡ b' → f a b ≡ f a' b'
    cong₂ f refl refl = refl

foldAppend :
  ∀ {A : Set} (weight : A → Nat) (xs ys : List A) →
  Reindex.foldNat weight (xs ++ ys)
  ≡ Reindex.foldNat weight xs + Reindex.foldNat weight ys
foldAppend weight [] ys = refl
foldAppend weight (x ∷ xs) ys =
  cong (weight x +_) (foldAppend weight xs ys)

foldSingleton :
  ∀ {A : Set} (weight : A → Nat) (x : A) →
  Reindex.foldNat weight (x ∷ []) ≡ weight x
foldSingleton weight x = NatP.+-identityʳ (weight x)

------------------------------------------------------------------------
-- Cardinality of the inner unit and partition fibres.

residualsForVectorLength :
  ∀ {n r : Nat}
    (bound : r Data.Nat.Base.≤ n)
    (pair : Positive.PositiveFactorPair r)
    (vector : Data.Vec.Base.Vec Nat (n Data.Nat.Base.∸ r)) →
  Reindex.listLength (Classical.residualsForVector bound pair vector)
  ≡ Positive.divisor pair
residualsForVectorLength bound pair vector =
  trans
    (Card.mapLength
      (Classical.classicalResidualKey bound pair vector)
      (Finite.allFin
        (Partition.partValue (Classical.ambientDivisorIndex bound pair))))
    (trans
      (Finite.allFinLength
        (Partition.partValue (Classical.ambientDivisorIndex bound pair)))
      (Classical.ambientDivisorPartValue bound pair))

residualsForPairLength :
  ∀ {n r : Nat}
    (bound : r Data.Nat.Base.≤ n)
    (pair : Positive.PositiveFactorPair r) →
  Reindex.listLength (Classical.residualsForPair bound pair)
  ≡ Positive.divisor pair * Regroup.partitionCount (n Data.Nat.Base.∸ r)
residualsForPairLength {n} {r} bound pair =
  trans
    (Card.concatMapLength
      (Classical.residualsForVector bound pair)
      (Enumeration.partitionMultiplicityVectors (n Data.Nat.Base.∸ r)))
    (trans
      (Reindex.foldPointwise
        (λ vector →
          Reindex.listLength
            (Classical.residualsForVector bound pair vector))
        (λ _ → Positive.divisor pair)
        (Enumeration.partitionMultiplicityVectors (n Data.Nat.Base.∸ r))
        (residualsForVectorLength bound pair))
      (foldConstantLength
        (Positive.divisor pair)
        (Enumeration.partitionMultiplicityVectors (n Data.Nat.Base.∸ r))))

------------------------------------------------------------------------
-- One r-block contributes factorPairWeightSum(r) * p(n-r).

residualBlockLength :
  ∀ {n r : Nat}
    (positive : suc zero Data.Nat.Base.≤ r)
    (bound : r Data.Nat.Base.≤ n) →
  Reindex.listLength (Classical.residualBlock positive bound)
  ≡ Regroup.Factor.factorPairWeightSum r
      * Regroup.partitionCount (n Data.Nat.Base.∸ r)
residualBlockLength {n} {r} positive bound =
  trans
    (Card.concatMapLength
      (Classical.residualsForPair bound)
      (Positive.positiveFactorPairs r positive))
    (trans
      (Reindex.foldPointwise
        (λ pair →
          Reindex.listLength (Classical.residualsForPair bound pair))
        (λ pair →
          Positive.divisor pair
          * Regroup.partitionCount (n Data.Nat.Base.∸ r))
        (Positive.positiveFactorPairs r positive)
        (residualsForPairLength bound))
      (trans
        (foldScaledRight
          Positive.divisor
          (Regroup.partitionCount (n Data.Nat.Base.∸ r))
          (Positive.positiveFactorPairs r positive))
        (cong
          (_* Regroup.partitionCount (n Data.Nat.Base.∸ r))
          (Positive.positiveFactorPairWeightSumEqualsFactor r positive))))

------------------------------------------------------------------------
-- Outer increasing-r recursion matches Hecke.oneTo exactly.

factorTerm : Nat → Nat → Nat
factorTerm n r =
  Regroup.Factor.factorPairWeightSum r
  * Regroup.partitionCount (n Data.Nat.Base.∸ r)

classicalResidualsUpToLength :
  (n current : Nat)
  (bound : current Data.Nat.Base.≤ n) →
  Reindex.listLength (Classical.classicalResidualsUpTo n current bound)
  ≡ Reindex.foldNat (factorTerm n) (Hecke.oneTo current)
classicalResidualsUpToLength n zero bound = refl
classicalResidualsUpToLength n (suc current) bound =
  trans
    (Card.appendLength
      (Classical.classicalResidualsUpTo n current
        (Classical.dropPositiveBound bound))
      (Classical.residualBlock (Data.Nat.Base.s≤s Data.Nat.Base.z≤n) bound))
    (trans
      (cong₂ _+_
        (classicalResidualsUpToLength n current
          (Classical.dropPositiveBound bound))
        (residualBlockLength
          (Data.Nat.Base.s≤s Data.Nat.Base.z≤n) bound))
      (sym oneToStep))
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C)
    {a a' : A} {b b' : B} →
    a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ f refl refl = refl

  oneToStep :
    Reindex.foldNat (factorTerm n) (Hecke.oneTo (suc current))
    ≡ Reindex.foldNat (factorTerm n) (Hecke.oneTo current)
      + factorTerm n (suc current)
  oneToStep =
    trans
      (foldAppend
        (factorTerm n)
        (Hecke.oneTo current)
        (suc current ∷ []))
      (cong
        (Reindex.foldNat (factorTerm n) (Hecke.oneTo current) +_)
        (foldSingleton (factorTerm n) (suc current)))

classicalFactorResidualEnumerationLength :
  (n : Nat) →
  Reindex.listLength (Classical.classicalFactorResidualEnumeration n)
  ≡ Regroup.factorPairGroupedRHS n
classicalFactorResidualEnumerationLength n =
  classicalResidualsUpToLength n n NatP.≤-refl

classicalFactorResidualUnitFold : Nat → Nat
classicalFactorResidualUnitFold n =
  Reindex.foldNat (λ _ → 1) (Classical.classicalFactorResidualEnumeration n)

classicalFactorResidualUnitFoldEqualsGroupedRHS :
  (n : Nat) →
  classicalFactorResidualUnitFold n ≡ Regroup.factorPairGroupedRHS n
classicalFactorResidualUnitFoldEqualsGroupedRHS n =
  trans
    (Reindex.foldOneIsLength (Classical.classicalFactorResidualEnumeration n))
    (classicalFactorResidualEnumerationLength n)

------------------------------------------------------------------------
-- The classical list now has the exact numeric RHS required by the recurrence.
------------------------------------------------------------------------
