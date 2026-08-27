module DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualDecompositionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- Reverse semantic decomposition of an admissible residual key.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_; _∸_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteNatVectorZeroPaddingExact as Pad
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.FiniteVectorPrefixSplitExact as Split
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityDeletionExact as Ambient
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityNormalizationExact as Normalize
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact as Admissible
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualEnumerationExact as Classical
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition

residualDecrement :
  ∀ {n : Nat} → Key.ResidualKey n → Nat
residualDecrement residual =
  Key.residualCopies residual
  * Partition.partValue (Key.residualIndex residual)

residualDivisorPositive :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  suc zero ≤ Partition.partValue (Key.residualIndex residual)
residualDivisorPositive residual = s≤s z≤n

residualDivisorBoundByDecrement :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  Partition.partValue (Key.residualIndex residual)
  ≤ residualDecrement residual
residualDivisorBoundByDecrement residual =
  NatP.m≤m+n
    (Partition.partValue (Key.residualIndex residual))
    (Key.residualPredecessor residual
      * Partition.partValue (Key.residualIndex residual))

residualDecrementPositive :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  suc zero ≤ residualDecrement residual
residualDecrementPositive residual =
  NatP.≤-trans
    (residualDivisorPositive residual)
    (residualDivisorBoundByDecrement residual)

residualFactorPair :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  Factor.PositiveFactorPair (residualDecrement residual)
residualFactorPair residual =
  Factor.positiveFactorPair
    (Partition.partValue (Key.residualIndex residual))
    (residualDivisorPositive residual)
    (residualDivisorBoundByDecrement residual)
    (Key.residualPredecessor residual)
    refl

------------------------------------------------------------------------
-- Admissibility gives r≤n and exact residual mass n-r.

residualDecrementAtMostGrade :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  Admissible.residualTotal residual ≡ n →
  residualDecrement residual ≤ n
residualDecrementAtMostGrade residual totalExact =
  subst
    (λ upper → residualDecrement residual ≤ upper)
    totalExact
    decrementBelowTotal
  where
  residualMass : Nat
  residualMass = Partition.weightedMass (Key.residualVector residual)

  decrementBelowTotal :
    residualDecrement residual ≤ residualMass + residualDecrement residual
  decrementBelowTotal =
    subst
      (λ upper → residualDecrement residual ≤ upper)
      (NatP.+-comm (residualDecrement residual) residualMass)
      (NatP.m≤m+n (residualDecrement residual) residualMass)

residualMassEqualsDifference :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  Admissible.residualTotal residual ≡ n →
  Partition.weightedMass (Key.residualVector residual)
  ≡ n ∸ residualDecrement residual
residualMassEqualsDifference residual totalExact =
  trans
    (sym
      (NatP.m+n∸n≡m
        (Partition.weightedMass (Key.residualVector residual))
        (residualDecrement residual)))
    (cong
      (_∸ residualDecrement residual)
      totalExact)

------------------------------------------------------------------------
-- Normalize the ambient residual vector to the canonical p(n-r) carrier.

residualDimensionDecomposition :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  Admissible.residualTotal residual ≡ n →
  (n ∸ residualDecrement residual) + residualDecrement residual ≡ n
residualDimensionDecomposition residual totalExact =
  Classical.differencePlus
    (residualDecrementAtMostGrade residual totalExact)

residualAmbientPartition :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  (totalExact : Admissible.residualTotal residual ≡ n) →
  Ambient.AmbientMultiplicityPartition
    ((n ∸ residualDecrement residual) + residualDecrement residual)
    (n ∸ residualDecrement residual)
residualAmbientPartition residual totalExact =
  Ambient.ambientMultiplicityPartition
    transported
    transportedMass
  where
  decomposition :
    (n ∸ residualDecrement residual) + residualDecrement residual ≡ n
  decomposition = residualDimensionDecomposition residual totalExact

  transported :
    Vec Nat ((n ∸ residualDecrement residual) + residualDecrement residual)
  transported =
    Normalize.transportVectorToDecomposition
      decomposition
      (Key.residualVector residual)

  transportedMass :
    Partition.weightedMass transported ≡ n ∸ residualDecrement residual
  transportedMass =
    trans
      (Normalize.transportWeightedMass
        decomposition (Key.residualVector residual))
      (residualMassEqualsDifference residual totalExact)

canonicalResidualPartition :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  (totalExact : Admissible.residualTotal residual ≡ n) →
  Partition.MultiplicityPartition (n ∸ residualDecrement residual)
canonicalResidualPartition residual totalExact =
  Normalize.normalizeAmbient
    (residualAmbientPartition residual totalExact)

------------------------------------------------------------------------
-- Literal reconstruction of the ambient residual representation.

transportForwardBackward :
  ∀ {left right : Nat}
    (equality : left ≡ right)
    (vector : Vec Nat right) →
  Classical.transportVectorForward equality
    (Normalize.transportVectorToDecomposition equality vector)
  ≡ vector
transportForwardBackward refl vector = refl

canonicalPaddingRecoversResidualVector :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  (totalExact : Admissible.residualTotal residual ≡ n) →
  Classical.padResidualVector
    (residualDecrementAtMostGrade residual totalExact)
    (Partition.multiplicities
      (canonicalResidualPartition residual totalExact))
  ≡ Key.residualVector residual
canonicalPaddingRecoversResidualVector {n} residual totalExact =
  trans
    (cong
      (Classical.transportVectorForward decomposition)
      appendCanonicalZeroEqualsTransported)
    (transportForwardBackward decomposition (Key.residualVector residual))
  where
  decrement : Nat
  decrement = residualDecrement residual

  bound : decrement ≤ n
  bound = residualDecrementAtMostGrade residual totalExact

  decomposition : (n ∸ decrement) + decrement ≡ n
  decomposition = Classical.differencePlus bound

  ambient :
    Ambient.AmbientMultiplicityPartition
      ((n ∸ decrement) + decrement)
      (n ∸ decrement)
  ambient = residualAmbientPartition residual totalExact

  transported : Vec Nat ((n ∸ decrement) + decrement)
  transported = Ambient.ambientMultiplicities ambient

  prefix : Vec Nat (n ∸ decrement)
  prefix = Split.takePrefix (n ∸ decrement) decrement transported

  appendCanonicalZeroEqualsTransported :
    Split.appendVec prefix (Split.zeroVec decrement) ≡ transported
  appendCanonicalZeroEqualsTransported =
    trans
      (cong
        (Split.appendVec prefix)
        (sym (Normalize.ambientTailZero ambient)))
      (Split.splitReconstruct (n ∸ decrement) decrement transported)

------------------------------------------------------------------------
-- The factor-pair coordinate reconstructed from an admissible residual returns
-- the original ambient Fin index exactly.

sucInjective : ∀ {left right : Nat} → suc left ≡ suc right → left ≡ right
sucInjective refl = refl

residualFactorAmbientIndex :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  (totalExact : Admissible.residualTotal residual ≡ n) →
  Classical.ambientDivisorIndex
    (residualDecrementAtMostGrade residual totalExact)
    (residualFactorPair residual)
  ≡ Key.residualIndex residual
residualFactorAmbientIndex residual totalExact =
  FinP.toℕ-injective
    (trans
      (Pad.widenFinToNat bound
        (Classical.divisorIndex (residualFactorPair residual)))
      divisorIndexToNat)
  where
  bound : residualDecrement residual ≤ _
  bound = residualDecrementAtMostGrade residual totalExact

  divisorIndexToNat :
    toℕ (Classical.divisorIndex (residualFactorPair residual))
    ≡ toℕ (Key.residualIndex residual)
  divisorIndexToNat =
    sucInjective
      (Classical.divisorIndexPartValue (residualFactorPair residual))

------------------------------------------------------------------------
-- Every admissible key therefore determines exactly the classical semantic
-- coordinates r, (v,k), a canonical partition of n-r, and unit u, and the
-- classical padding/index maps recover its ambient representation literally.
------------------------------------------------------------------------
