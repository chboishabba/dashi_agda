module DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualPermutationExact where

------------------------------------------------------------------------
-- Exact proof-relevant permutation between the conventional r=k*v residual
-- enumeration and the independently filtered admissible residual normal form.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact as Admissible
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalAdmissibleMembershipExact as Membership
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualEnumerationExact as Classical
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualUniqueExact as ClassicalUnique

classicalAdmissiblePermutation :
  (n : Nat) →
  Classical.classicalFactorResidualEnumeration n
  Perm.↭
  Admissible.admissibleResidualEnumeration n
classicalAdmissiblePermutation n =
  Reindex.uniqueMembershipEquivalenceToPermutation
    (ClassicalUnique.classicalFactorResidualEnumerationUnique n)
    (Admissible.admissibleResidualUnique n)
    Membership.classicalToAdmissible
    Membership.admissibleToClassical

classicalAdmissibleUnitFold :
  (n : Nat) →
  Reindex.foldNat (λ _ → 1)
    (Classical.classicalFactorResidualEnumeration n)
  ≡ Reindex.foldNat (λ _ → 1)
    (Admissible.admissibleResidualEnumeration n)
classicalAdmissibleUnitFold n =
  Reindex.foldPermutationInvariant
    (λ _ → 1)
    (classicalAdmissiblePermutation n)

------------------------------------------------------------------------
-- Both independent finite presentations are now the same list up to exact
-- proof-relevant permutation.
------------------------------------------------------------------------
