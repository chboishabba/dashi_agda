module DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualSoundExact where

------------------------------------------------------------------------
-- Every entry of the conventional r=k*v residual enumeration satisfies the
-- independently stated admissibility equation
--
--   mass(mu) + k*v = n.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using ()
open import Data.Nat.Base using (_≤_; _∸_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact as Admissible
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualEnumerationExact as Classical
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyCardinalityExact as Cardinality
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Positive
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition

residualsForVectorSound :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Positive.PositiveFactorPair r)
    (vector : Vec Nat (n ∸ r)) →
  Partition.weightedMass vector ≡ n ∸ r →
  ∀ {residual : Key.ResidualKey n} →
  residual ∈ Classical.residualsForVector bound pair vector →
  Admissible.residualTotal residual ≡ n
residualsForVectorSound bound pair vector vectorMass {residual} member
  with ∈-map⁻ (Classical.classicalResidualKey bound pair vector) member
... | unit , unitMember , residualEqualsConstructed =
  subst
    (λ candidate → Admissible.residualTotal candidate ≡ _)
    (sym residualEqualsConstructed)
    (Classical.classicalResidualTotalExact
      bound pair vector vectorMass unit)

residualsForPairSound :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Positive.PositiveFactorPair r)
    {residual : Key.ResidualKey n} →
  residual ∈ Classical.residualsForPair bound pair →
  Admissible.residualTotal residual ≡ n
residualsForPairSound {n} {r} bound pair member
  with Product.concatMapMemberInverse
         (Classical.residualsForVector bound pair) member
... | vector , vectorMember , residualMember =
  residualsForVectorSound
    bound pair vector
    (Cardinality.partitionVectorMassSound vectorMember)
    residualMember

residualBlockSound :
  ∀ {n r : Nat}
    (positive : suc zero ≤ r)
    (bound : r ≤ n)
    {residual : Key.ResidualKey n} →
  residual ∈ Classical.residualBlock positive bound →
  Admissible.residualTotal residual ≡ n
residualBlockSound positive bound member
  with Product.concatMapMemberInverse
         (Classical.residualsForPair bound) member
... | pair , pairMember , residualMember =
  residualsForPairSound bound pair residualMember

classicalResidualsUpToSound :
  ∀ {n current : Nat}
    (bound : current ≤ n)
    {residual : Key.ResidualKey n} →
  residual ∈ Classical.classicalResidualsUpTo n current bound →
  Admissible.residualTotal residual ≡ n
classicalResidualsUpToSound {current = zero} z≤n ()
classicalResidualsUpToSound {n} {suc current} bound member
  with ∈-++⁻
         (Classical.classicalResidualsUpTo n current
           (Classical.dropPositiveBound bound))
         member
... | inj₁ earlier =
  classicalResidualsUpToSound
    (Classical.dropPositiveBound bound) earlier
... | inj₂ blockMember =
  residualBlockSound (s≤s z≤n) bound blockMember

classicalFactorResidualEnumerationSound :
  ∀ {n : Nat} {residual : Key.ResidualKey n} →
  residual ∈ Classical.classicalFactorResidualEnumeration n →
  Admissible.residualTotal residual ≡ n
classicalFactorResidualEnumerationSound {n} =
  classicalResidualsUpToSound NatP.≤-refl

------------------------------------------------------------------------
-- The classical list is therefore contained in the admissible normal form.
------------------------------------------------------------------------
