module DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualCompletenessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- Every independently admissible residual key occurs in the conventional
-- r=k*v / partition-of-(n-r) / unit enumeration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Base using (_≤_; _∸_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _×_; _,_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualDecompositionExact as Decompose
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact as Admissible
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualEnumerationExact as Classical
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Transport the original unit to the scanned factor pair's recovered index.

transportUnitToClassical :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (residual : Key.ResidualKey n) →
  Classical.ambientDivisorIndex bound pair ≡ Key.residualIndex residual →
  Fin (Partition.partValue (Classical.ambientDivisorIndex bound pair))
transportUnitToClassical bound pair residual indexExact =
  subst
    (λ index → Fin (Partition.partValue index))
    (sym indexExact)
    (Key.residualUnit residual)

classicalKeyRecoversResidual :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (vector : Vec.Vec Nat (n ∸ r))
    (residual : Key.ResidualKey n)
    (vectorExact : Classical.padResidualVector bound vector
      ≡ Key.residualVector residual)
    (indexExact : Classical.ambientDivisorIndex bound pair
      ≡ Key.residualIndex residual)
    (predecessorExact : Factor.predecessor pair
      ≡ Key.residualPredecessor residual) →
  Classical.classicalResidualKey
    bound pair vector
    (transportUnitToClassical bound pair residual indexExact)
  ≡ residual
classicalKeyRecoversResidual
    bound pair vector
    (residualVector , residualIndex , residualPredecessor , residualUnit)
    vectorExact indexExact predecessorExact
  with vectorExact | indexExact | predecessorExact
... | refl | refl | refl = refl

------------------------------------------------------------------------
-- The scanned factor pair can be selected with the exact proof-free
-- divisor/predecessor coordinates reconstructed from the admissible key.

selectedFactorPair :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  Σ (Factor.PositiveFactorPair (Decompose.residualDecrement residual)) λ pair →
    (pair ∈ Factor.positiveFactorPairs
      (Decompose.residualDecrement residual)
      (Decompose.residualDecrementPositive residual))
    ×
    ((Factor.divisor pair
      ≡ Partition.partValue (Key.residualIndex residual))
    ×
    (Factor.predecessor pair
      ≡ Key.residualPredecessor residual))
selectedFactorPair residual =
  Factor.positiveFactorPairCoordinatesComplete
    (Decompose.residualDecrement residual)
    (Decompose.residualDecrementPositive residual)
    (Decompose.residualDivisorPositive residual)
    (Decompose.residualDivisorBoundByDecrement residual)
    refl

selectedPairAmbientIndex :
  ∀ {n : Nat}
    (residual : Key.ResidualKey n)
    (totalExact : Admissible.residualTotal residual ≡ n)
    (pair : Factor.PositiveFactorPair (Decompose.residualDecrement residual)) →
  Factor.divisor pair ≡ Partition.partValue (Key.residualIndex residual) →
  Classical.ambientDivisorIndex
    (Decompose.residualDecrementAtMostGrade residual totalExact)
    pair
  ≡ Key.residualIndex residual
selectedPairAmbientIndex residual totalExact pair divisorExact =
  FinP.toℕ-injective
    (sucInjective
      (trans
        (Classical.ambientDivisorPartValue bound pair)
        divisorExact))
  where
  bound = Decompose.residualDecrementAtMostGrade residual totalExact

  sucInjective :
    ∀ {left right : Nat} → suc left ≡ suc right → left ≡ right
  sucInjective refl = refl

------------------------------------------------------------------------
-- Canonical partition and unit membership put the reconstructed key inside the
-- selected factor-pair block.

admissibleResidualInBlock :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  (totalExact : Admissible.residualTotal residual ≡ n) →
  residual ∈
    Classical.residualBlock
      (Decompose.residualDecrementPositive residual)
      (Decompose.residualDecrementAtMostGrade residual totalExact)
admissibleResidualInBlock residual totalExact
  with selectedFactorPair residual
... | pair , (pairMember , (divisorExact , predecessorExact)) =
  subst
    (λ candidate → candidate ∈ Classical.residualBlock positive bound)
    keyExact
    blockMember
  where
  decrement = Decompose.residualDecrement residual
  positive = Decompose.residualDecrementPositive residual
  bound = Decompose.residualDecrementAtMostGrade residual totalExact

  canonical = Decompose.canonicalResidualPartition residual totalExact
  vector = Partition.multiplicities canonical

  vectorMember :
    vector ∈ Enumeration.partitionMultiplicityVectors (n ∸ decrement)
  vectorMember = Enumeration.partitionMultiplicityVectorComplete canonical

  indexExact :
    Classical.ambientDivisorIndex bound pair ≡ Key.residualIndex residual
  indexExact = selectedPairAmbientIndex residual totalExact pair divisorExact

  unit = transportUnitToClassical bound pair residual indexExact

  unitMember :
    unit ∈ Finite.allFin
      (Partition.partValue (Classical.ambientDivisorIndex bound pair))
  unitMember = Finite.allFinComplete unit

  vectorBlockMember :
    Classical.classicalResidualKey bound pair vector unit
    ∈ Classical.residualsForVector bound pair vector
  vectorBlockMember = Product.mapMember
    (Classical.classicalResidualKey bound pair vector)
    unitMember

  pairBlockMember :
    Classical.classicalResidualKey bound pair vector unit
    ∈ Classical.residualsForPair bound pair
  pairBlockMember =
    Product.concatMapMember
      (Classical.residualsForVector bound pair)
      vectorMember
      vectorBlockMember

  blockMember :
    Classical.classicalResidualKey bound pair vector unit
    ∈ Classical.residualBlock positive bound
  blockMember =
    Product.concatMapMember
      (Classical.residualsForPair bound)
      pairMember
      pairBlockMember

  keyExact :
    Classical.classicalResidualKey bound pair vector unit ≡ residual
  keyExact =
    classicalKeyRecoversResidual
      bound pair vector residual
      (Decompose.canonicalPaddingRecoversResidualVector residual totalExact)
      indexExact
      predecessorExact

------------------------------------------------------------------------
-- Finally place the r-block inside the full increasing-r enumeration.

admissibleResidualInClassicalEnumeration :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  residual ∈ Admissible.admissibleResidualEnumeration n →
  residual ∈ Classical.classicalFactorResidualEnumeration n
admissibleResidualInClassicalEnumeration {n} residual member =
  Classical.residualBlockMemberUpTo
    NatP.≤-refl
    (Decompose.residualDecrementPositive residual)
    (Decompose.residualDecrementAtMostGrade residual totalExact)
    (admissibleResidualInBlock residual totalExact)
  where
  totalExact : Admissible.residualTotal residual ≡ n
  totalExact = Admissible.admissibleResidualSound member

------------------------------------------------------------------------
-- No equality of proof fields is used: only residual vector/index/predecessor/
-- unit coordinates are reconstructed literally.
------------------------------------------------------------------------
