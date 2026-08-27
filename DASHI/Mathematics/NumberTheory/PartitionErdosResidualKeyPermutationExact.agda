module DASHI.Mathematics.NumberTheory.PartitionErdosResidualKeyPermutationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- EXACT RESIDUAL NORMAL-FORM PERMUTATION
--
-- The strict deletion-image enumeration and the independently generated
-- admissible residual-key enumeration have exactly the same members.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Fin.Base using (Fin; fromℕ<; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.Nat.Properties as NatP
open import Data.Nat.Properties using (_≟_)
open import Data.Vec.Base using (Vec)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact as Admissible
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyCardinalityExact as Cardinality
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyRoundTripExact as RoundTrip
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeySystemExact as System
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityDeletionMassExact as Mass
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Selection completeness.

selectAdmissibleComplete :
  ∀ {n} {residual : Key.ResidualKey n}
    {residuals : List (Key.ResidualKey n)} →
  residual ∈ residuals →
  Admissible.residualTotal residual ≡ n →
  residual ∈ Admissible.selectAdmissible {n} residuals
selectAdmissibleComplete {residuals = []} () exact
selectAdmissibleComplete {n} {residual} {residuals = head ∷ tail}
    (Any.here equality) exact
  with Admissible.residualTotal head ≟ n
... | yes _ = Any.here equality
... | no contradiction =
  Data.Empty.⊥-elim
    (contradiction
      (subst
        (λ candidate → Admissible.residualTotal candidate ≡ n)
        equality
        exact))
selectAdmissibleComplete {n} {residual} {residuals = head ∷ tail}
    (Any.there member) exact
  with Admissible.residualTotal head ≟ n
... | yes _ = Any.there (selectAdmissibleComplete member exact)
... | no _ = selectAdmissibleComplete member exact

------------------------------------------------------------------------
-- Finite predecessor membership from j<n.

finitePredecessorListed :
  ∀ {n} (predecessor : Nat) →
  predecessor NatP.< n →
  predecessor ∈ Admissible.finitePredecessors n
finitePredecessorListed predecessor bound =
  subst
    (λ value → value ∈ Admissible.finitePredecessors _)
    (FinP.toℕ-fromℕ< bound)
    (Dep.mapMember toℕ
      (Finite.allFinComplete (fromℕ< bound)))

------------------------------------------------------------------------
-- Raw residual-key completeness from its component memberships.

rawResidualListed :
  ∀ {n} (residual : Key.ResidualKey n) →
  Key.residualVector residual ∈ Enumeration.proofBoundedVectors n n →
  Key.residualPredecessor residual ∈ Admissible.finitePredecessors n →
  residual ∈ Admissible.rawResidualEnumeration n
rawResidualListed (vector , index , predecessor , unit)
    vectorMember predecessorMember =
  Dep.dependentPairsMember Admissible.indexResidualEnumeration
    vectorMember
    (Dep.dependentPairsMember Admissible.predecessorUnitEnumeration
      (Finite.allFinComplete index)
      (Dep.dependentPairsMember
        (λ _ → Finite.allFin (Partition.partValue index))
        predecessorMember
        (Finite.allFinComplete unit)))

------------------------------------------------------------------------
-- Forward: every deleted canonical cell is independently admissible.

deletedCellAdmissible :
  ∀ {n} (cell : Key.CellKey n) →
  cell ∈ Key.cellKeyEnumeration n →
  Key.deleteKey cell ∈ Admissible.admissibleResidualEnumeration n
deletedCellAdmissible {n} cell cellMember =
  selectAdmissibleComplete rawMember deletionExact
  where
  sourceVectorMember :
    Key.cellVector cell ∈ Enumeration.partitionMultiplicityVectors n
  sourceVectorMember = Dep.dependentPairsFirstMember cellMember

  sourceMass : Partition.weightedMass (Key.cellVector cell) ≡ n
  sourceMass = Cardinality.partitionVectorMassSound sourceVectorMember

  sourcePartition : Partition.MultiplicityPartition n
  sourcePartition =
    Partition.multiplicityPartition (Key.cellVector cell) sourceMass

  deletionExact :
    Admissible.residualTotal (Key.deleteKey cell) ≡ n
  deletionExact =
    Mass.partitionDeletionMass
      sourcePartition
      (Key.cellCopies cell)
      (Key.cellIndex cell)
      (RoundTrip.cellCopiesAvailable cell)

  residualMass≤n :
    Partition.weightedMass (Key.residualVector (Key.deleteKey cell)) NatP.≤ n
  residualMass≤n =
    subst
      (λ upper →
        Partition.weightedMass (Key.residualVector (Key.deleteKey cell)) NatP.≤ upper)
      deletionExact
      (NatP.m≤m+n
        (Partition.weightedMass (Key.residualVector (Key.deleteKey cell)))
        (Key.residualCopies (Key.deleteKey cell)
          * Partition.partValue (Key.residualIndex (Key.deleteKey cell))))

  residualPointwiseBound :
    ∀ index →
    Partition.lookupMultiplicity index (Key.residualVector (Key.deleteKey cell))
    NatP.≤ n
  residualPointwiseBound index =
    NatP.≤-trans
      (Partition.coordinate≤weightedMass
        index (Key.residualVector (Key.deleteKey cell)))
      residualMass≤n

  residualVectorMember :
    Key.residualVector (Key.deleteKey cell)
    ∈ Enumeration.proofBoundedVectors n n
  residualVectorMember =
    Enumeration.representedVectorListed
      (Enumeration.boundedRepresentationFromPointwise
        (Key.residualVector (Key.deleteKey cell))
        residualPointwiseBound)

  predecessor<n : Key.residualPredecessor (Key.deleteKey cell) NatP.< n
  predecessor<n =
    NatP.<-≤-trans
      (FinP.toℕ<n (Key.cellOccurrence cell))
      (Partition.partitionCoordinateAtMostGrade
        sourcePartition (Key.cellIndex cell))

  predecessorMember :
    Key.residualPredecessor (Key.deleteKey cell)
    ∈ Admissible.finitePredecessors n
  predecessorMember =
    finitePredecessorListed
      (Key.residualPredecessor (Key.deleteKey cell))
      predecessor<n

  rawMember :
    Key.deleteKey cell ∈ Admissible.rawResidualEnumeration n
  rawMember =
    rawResidualListed (Key.deleteKey cell)
      residualVectorMember predecessorMember

------------------------------------------------------------------------
-- Backward: every independently admissible residual reconstructs a canonical
-- mass-n source key, whose deletion is literally the original residual.

admissibleResidualInDeletionImage :
  ∀ {n} (residual : Key.ResidualKey n) →
  residual ∈ Admissible.admissibleResidualEnumeration n →
  residual ∈ System.residualKeyEnumeration n
admissibleResidualInDeletionImage {n} residual member =
  subst
    (λ candidate → candidate ∈ System.residualKeyEnumeration n)
    (RoundTrip.deleteInsertKey residual)
    (∈-map⁺ Key.deleteKey sourceCellMember)
  where
  totalExact : Admissible.residualTotal residual ≡ n
  totalExact = Admissible.admissibleResidualSound member

  sourceMass :
    Partition.weightedMass (RoundTrip.insertedVector residual) ≡ n
  sourceMass =
    trans
      (Mass.partitionInsertionMass
        (Key.residualVector residual)
        (Key.residualCopies residual)
        (Key.residualIndex residual))
      totalExact

  sourcePartition : Partition.MultiplicityPartition n
  sourcePartition =
    Partition.multiplicityPartition
      (RoundTrip.insertedVector residual)
      sourceMass

  sourceVectorMember :
    RoundTrip.insertedVector residual
    ∈ Enumeration.partitionMultiplicityVectors n
  sourceVectorMember =
    Enumeration.partitionMultiplicityVectorComplete sourcePartition

  sourceCellMember :
    RoundTrip.insertKey residual ∈ Key.cellKeyEnumeration n
  sourceCellMember =
    Key.cellKeyListed (RoundTrip.insertKey residual) sourceVectorMember

------------------------------------------------------------------------
-- Membership equivalence between the two unique finite lists.

imageToAdmissible :
  ∀ {n} {residual : Key.ResidualKey n} →
  residual ∈ System.residualKeyEnumeration n →
  residual ∈ Admissible.admissibleResidualEnumeration n
imageToAdmissible {residual = residual} member
  with Data.List.Membership.Propositional.Properties.∈-map⁻
         Key.deleteKey member
... | cell , cellMember , residualEqualsDeleted =
  subst
    (λ candidate → candidate ∈ Admissible.admissibleResidualEnumeration _)
    (sym residualEqualsDeleted)
    (deletedCellAdmissible cell cellMember)

admissibleToImage :
  ∀ {n} {residual : Key.ResidualKey n} →
  residual ∈ Admissible.admissibleResidualEnumeration n →
  residual ∈ System.residualKeyEnumeration n
admissibleToImage {residual = residual} =
  admissibleResidualInDeletionImage residual

residualNormalFormPermutation :
  (n : Nat) →
  System.residualKeyEnumeration n
  Data.List.Relation.Binary.Permutation.Propositional.↭
  Admissible.admissibleResidualEnumeration n
residualNormalFormPermutation n =
  Reindex.uniqueMembershipEquivalenceToPermutation
    (System.residualKeyEnumerationUnique n)
    (Admissible.admissibleResidualUnique n)
    imageToAdmissible
    admissibleToImage

------------------------------------------------------------------------
-- The strict residual image now has an independently generated normal form.
------------------------------------------------------------------------
