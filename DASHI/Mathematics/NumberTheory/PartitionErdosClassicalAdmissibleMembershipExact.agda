module DASHI.Mathematics.NumberTheory.PartitionErdosClassicalAdmissibleMembershipExact where

------------------------------------------------------------------------
-- The conventional r=k*v residual enumeration and the independently filtered
-- admissible residual normal form have exactly the same proof-free members.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Membership.Propositional using (_∈_)

import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact as Admissible
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualCompletenessExact as Complete
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualEnumerationExact as Classical
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualSoundExact as Sound
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionErdosResidualAdmissibilityCompleteExact as ExactTotal

classicalToAdmissible :
  ∀ {n : Nat} {residual : Key.ResidualKey n} →
  residual ∈ Classical.classicalFactorResidualEnumeration n →
  residual ∈ Admissible.admissibleResidualEnumeration n
classicalToAdmissible {residual = residual} member =
  ExactTotal.exactResidualTotalImpliesAdmissible residual
    (Sound.classicalFactorResidualEnumerationSound member)

admissibleToClassical :
  ∀ {n : Nat} {residual : Key.ResidualKey n} →
  residual ∈ Admissible.admissibleResidualEnumeration n →
  residual ∈ Classical.classicalFactorResidualEnumeration n
admissibleToClassical {residual = residual} =
  Complete.admissibleResidualInClassicalEnumeration residual

------------------------------------------------------------------------
-- The next owner combines this membership equivalence with duplicate-freedom
-- of the classical enumeration to obtain a proof-relevant list permutation.
------------------------------------------------------------------------
