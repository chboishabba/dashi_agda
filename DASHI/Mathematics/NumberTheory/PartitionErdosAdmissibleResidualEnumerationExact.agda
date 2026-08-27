module DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- INDEPENDENT RESIDUAL NORMAL FORM
--
-- Enumerate proof-free residual keys independently of source partitions:
--
--   (mu , v , j , u)
--
-- with mu a bounded ambient multiplicity vector, v a part coordinate,
-- j in {0,...,n-1}, u : Fin(v), then retain exactly the keys satisfying
--
--   mass(mu) + (j+1)*v = n.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (Σ; _×_)
open import Data.Vec.Base using (Vec)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Finite Nat predecessors 0,...,n-1.

finitePredecessors : Nat → List Nat
finitePredecessors n = map toℕ (Finite.allFin n)

finitePredecessorsUnique : (n : Nat) → Unique (finitePredecessors n)
finitePredecessorsUnique n =
  UniqueP.map⁺ FinP.toℕ-injective (Finite.allFinUnique n)

------------------------------------------------------------------------
-- Raw finite residual carrier.

predecessorUnitEnumeration :
  ∀ {n} (index : Fin n) →
  List (Nat × Fin (Partition.partValue index))
predecessorUnitEnumeration {n} index =
  Dep.dependentPairs
    (finitePredecessors n)
    (λ _ → Finite.allFin (Partition.partValue index))

indexResidualEnumeration :
  ∀ {n} (vector : Vec Nat n) →
  List
    (Σ (Fin n) λ index →
      Nat × Fin (Partition.partValue index))
indexResidualEnumeration {n} vector =
  Dep.dependentPairs
    (Finite.allFin n)
    predecessorUnitEnumeration

rawResidualEnumeration : (n : Nat) → List (Key.ResidualKey n)
rawResidualEnumeration n =
  Dep.dependentPairs
    (Enumeration.proofBoundedVectors n n)
    indexResidualEnumeration

predecessorUnitUnique :
  ∀ {n} (index : Fin n) →
  Unique (predecessorUnitEnumeration index)
predecessorUnitUnique {n} index =
  Dep.dependentPairsUnique
    (λ _ → Finite.allFin (Partition.partValue index))
    (finitePredecessorsUnique n)
    (λ _ → Finite.allFinUnique (Partition.partValue index))

indexResidualUnique :
  ∀ {n} (vector : Vec Nat n) →
  Unique (indexResidualEnumeration vector)
indexResidualUnique {n} vector =
  Dep.dependentPairsUnique
    predecessorUnitEnumeration
    (Finite.allFinUnique n)
    predecessorUnitUnique

rawResidualUnique : (n : Nat) → Unique (rawResidualEnumeration n)
rawResidualUnique n =
  Dep.dependentPairsUnique
    indexResidualEnumeration
    (Enumeration.proofBoundedVectorsUnique n n)
    indexResidualUnique

------------------------------------------------------------------------
-- Exact grade-n admissibility.

residualTotal : ∀ {n} → Key.ResidualKey n → Nat
residualTotal residual =
  Partition.weightedMass (Key.residualVector residual)
  + Key.residualCopies residual * Partition.partValue (Key.residualIndex residual)

selectAdmissible :
  {n : Nat} → List (Key.ResidualKey n) → List (Key.ResidualKey n)
selectAdmissible {n} [] = []
selectAdmissible {n} (residual ∷ residuals)
  with residualTotal residual ≟ n
... | yes _ = residual ∷ selectAdmissible residuals
... | no _ = selectAdmissible residuals

admissibleResidualEnumeration :
  (n : Nat) → List (Key.ResidualKey n)
admissibleResidualEnumeration n =
  selectAdmissible (rawResidualEnumeration n)

selectedAdmissibleMemberOriginal :
  ∀ {n} {residual : Key.ResidualKey n} {residuals} →
  residual ∈ selectAdmissible {n} residuals → residual ∈ residuals
selectedAdmissibleMemberOriginal {residuals = []} ()
selectedAdmissibleMemberOriginal {n} {residuals = head ∷ tail} member
  with residualTotal head ≟ n
... | yes _ with member
...   | Any.here equality = Any.here equality
...   | Any.there rest = Any.there (selectedAdmissibleMemberOriginal rest)
... | no _ = Any.there (selectedAdmissibleMemberOriginal member)

selectAdmissibleUnique :
  ∀ {n} {residuals : List (Key.ResidualKey n)} →
  Unique residuals → Unique (selectAdmissible {n} residuals)
selectAdmissibleUnique {residuals = []} AllPairs.[] = AllPairs.[]
selectAdmissibleUnique {n} {residuals = head ∷ tail}
    (AllPairs._∷_ fresh rest)
  with residualTotal head ≟ n
... | yes _ =
  AllPairs._∷_
    (All.tabulate
      (λ member →
        All.lookup fresh (selectedAdmissibleMemberOriginal member)))
    (selectAdmissibleUnique rest)
... | no _ = selectAdmissibleUnique rest

admissibleResidualUnique :
  (n : Nat) → Unique (admissibleResidualEnumeration n)
admissibleResidualUnique n =
  selectAdmissibleUnique (rawResidualUnique n)

selectAdmissibleSound :
  ∀ {n} {residual : Key.ResidualKey n} {residuals} →
  residual ∈ selectAdmissible {n} residuals →
  residualTotal residual ≡ n
selectAdmissibleSound {residuals = []} ()
selectAdmissibleSound {n} {residual} {residuals = head ∷ tail} member
  with residualTotal head ≟ n
... | yes exact with member
...   | Any.here equality =
  subst (λ candidate → residualTotal candidate ≡ n) (sym equality) exact
...   | Any.there rest = selectAdmissibleSound rest
... | no _ = selectAdmissibleSound member

admissibleResidualSound :
  ∀ {n} {residual : Key.ResidualKey n} →
  residual ∈ admissibleResidualEnumeration n →
  residualTotal residual ≡ n
admissibleResidualSound = selectAdmissibleSound

------------------------------------------------------------------------
-- The independent list is finite and duplicate-free.  Membership equivalence
-- with the deletion-image residual list is proved in the next owner.
------------------------------------------------------------------------
