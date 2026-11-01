module DASHI.Mathematics.NumberTheory.PartitionErdosResidualAdmissibilityCompleteExact where

------------------------------------------------------------------------
-- Any proof-free residual key of ambient grade n satisfying the exact total
-- equation is automatically present in the independently generated admissible
-- residual enumeration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Membership.Propositional using (_∈_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as FinitePositive
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualDecompositionExact as Decompose
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact as Admissible
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionErdosResidualKeyPermutationExact as ResidualPermutation
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

exactResidualTotalImpliesAdmissible :
  ∀ {n : Nat} (residual : Key.ResidualKey n) →
  Admissible.residualTotal residual ≡ n →
  residual ∈ Admissible.admissibleResidualEnumeration n
exactResidualTotalImpliesAdmissible {n} residual totalExact =
  ResidualPermutation.selectAdmissibleComplete rawMember totalExact
  where
  residualMass≤n :
    Partition.weightedMass (Key.residualVector residual) NatP.≤ n
  residualMass≤n =
    NatP.≤-trans
      (NatP.m≤m+n
        (Partition.weightedMass (Key.residualVector residual))
        (Decompose.residualDecrement residual))
      (NatP.≤-reflexive totalExact)

  residualPointwiseBound :
    ∀ index →
    Partition.lookupMultiplicity index (Key.residualVector residual)
    NatP.≤ n
  residualPointwiseBound index =
    NatP.≤-trans
      (Partition.coordinate≤weightedMass
        index (Key.residualVector residual))
      residualMass≤n

  residualVectorMember :
    Key.residualVector residual ∈ Enumeration.proofBoundedVectors n n
  residualVectorMember =
    Enumeration.representedVectorListed
      (Enumeration.boundedRepresentationFromPointwise
        (Key.residualVector residual)
        residualPointwiseBound)

  predecessor<n : Key.residualPredecessor residual NatP.< n
  predecessor<n =
    NatP.<-≤-trans
      (FinitePositive.predecessorBelowProduct
        (Decompose.residualFactorPair residual))
      (Decompose.residualDecrementAtMostGrade residual totalExact)

  predecessorMember :
    Key.residualPredecessor residual
    ∈ Admissible.finitePredecessors n
  predecessorMember =
    ResidualPermutation.finitePredecessorListed
      (Key.residualPredecessor residual)
      predecessor<n

  rawMember : residual ∈ Admissible.rawResidualEnumeration n
  rawMember =
    ResidualPermutation.rawResidualListed residual
      residualVectorMember predecessorMember

------------------------------------------------------------------------
-- This theorem is source-neutral finite arithmetic; Erdős enters when a
-- classical or deletion construction supplies the exact total equation.
------------------------------------------------------------------------
