module DASHI.Mathematics.NumberTheory.PartitionFiniteGrowthEnvelopeExact where

------------------------------------------------------------------------
-- COARSE FINITE GROWTH ENVELOPE FOR THE CANONICAL PARTITION COUNT
--
-- Every grade-n multiplicity vector lies in the finite box {0,...,n}^n.
-- Since the canonical partition enumeration is an exact mass filter of that
-- unique box,
--
--   p_DASHI(n) <= (n+1)^n.
--
-- This is intentionally coarse.  Its purpose is to provide a fully finite
-- growth majorant before the Erdos/Bishop exponential estimates begin.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; trans)
import Data.Vec.Base as Vec

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FiniteProductCardinalityExact as ProductCard
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Exact size of the proof-oriented Nat box.  Mapping Fin coordinates to Nat
-- preserves list length.

proofBoundedVectorsLength :
  (dimension bound : Nat) →
  Reindex.listLength (Enumeration.proofBoundedVectors dimension bound)
  ≡ Hecke.powNat (suc bound) dimension
proofBoundedVectorsLength dimension bound =
  trans
    (Card.mapLength
      Enumeration.finVectorToNat
      (Enumeration.finBoundedVectors dimension bound))
    (ProductCard.uniqueFinVectorPowerLength (suc bound) dimension)

------------------------------------------------------------------------
-- Exact filtering never increases list length.

selectMassLengthBound :
  ∀ {n : Nat} (vectors : List (Vec.Vec Nat n)) →
  Reindex.listLength (Enumeration.selectMass {n} vectors)
  ≤ Reindex.listLength vectors
selectMassLengthBound {n} [] = z≤n
selectMassLengthBound {n} (vector ∷ vectors)
  with Partition.weightedMass vector ≟ n
... | yes massExact =
  s≤s (selectMassLengthBound vectors)
... | no notMass =
  NatP.≤-step (selectMassLengthBound vectors)

------------------------------------------------------------------------
-- Canonical partition count is therefore bounded by the full box size.

canonicalPartitionCount : Nat → Nat
canonicalPartitionCount n =
  Reindex.listLength (Enumeration.partitionMultiplicityVectors n)

canonicalPartitionCountBoxBound :
  (n : Nat) →
  canonicalPartitionCount n ≤ Hecke.powNat (suc n) n
canonicalPartitionCountBoxBound n =
  subst
    (λ upper → canonicalPartitionCount n ≤ upper)
    (proofBoundedVectorsLength n n)
    (selectMassLengthBound (Enumeration.proofBoundedVectors n n))

------------------------------------------------------------------------
-- No real/exponential analysis occurs here.  The sharp Erdos upper envelope
-- exp(c*sqrt(n)) is a strictly stronger downstream theorem.
------------------------------------------------------------------------
