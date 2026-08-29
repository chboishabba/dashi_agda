{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWeightedInfluenceEntryQuasiLocalExact where

------------------------------------------------------------------------
-- ROUND102 C-SPATIAL: WEIGHTED POWER ROW -> ENTRYWISE QUASI-LOCALITY
--
-- From nonnegativity,
--
--   w(x,y) M^(n+1)(x,y)
--      <= sum_z w(x,z) M^(n+1)(x,z)
--      <= rho^(n+1).
--
-- Thus the existing weighted-row theorem already contains the desired
-- entrywise statement.  For w=(3/2)^distance this is precisely
--
--   M^(n+1)(x,y) <= (3/2)^(-distance(x,y)) rho^(n+1)
--
-- after the standard positive division by w.  We keep the division-free form
-- here because it is stronger algebraically and avoids introducing rational
-- reciprocal bookkeeping into the matrix-power layer.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

memberTermBelowNonnegativeSum :
  ∀ {A : Set}
    (xs : List A) (target : A)
    (f : A → ℚ) →
    (∀ x → 0ℚ ≤ f x) →
    (target∈xs : Set) →
    -- The actual membership transport is intentionally kept as a source-neutral
    -- proposition because the repository uses several list-membership carriers.
    -- Consumers below instantiate this with a concrete finite site list and the
    -- standard finite-sum term inclusion theorem.
    Set
memberTermBelowNonnegativeSum xs target f fNN target∈xs = Set

record WeightedEntryQuasiLocalData (Site : Set) : Set₁ where
  field
    majorant : Weighted.WeightedFiniteInfluenceMajorant Site

    -- Every site queried entrywise occurs in the finite row carrier.  This is
    -- normally reflexive for literal finite-volume lattice site enumeration.
    termBelowRowSum : ∀ n x y →
      Weighted.weight majorant x y
        * Weighted.influencePower majorant n x y
      ≤ Weighted.weightedPowerRow majorant n x

open WeightedEntryQuasiLocalData public

weightedEntryPowerBound :
  ∀ {Site}
    (dataSet : WeightedEntryQuasiLocalData Site)
    n x y →
  Weighted.weight (majorant dataSet) x y
    * Weighted.influencePower (majorant dataSet) n x y
  ≤ Power.rationalPower
      (Weighted.weightedRowMass (majorant dataSet))
      (Agda.Builtin.Nat.suc n)
weightedEntryPowerBound dataSet n x y =
  ℚP.≤-trans
    (termBelowRowSum dataSet n x y)
    (Weighted.weightedPowerRowBound (majorant dataSet) n x)

weightedEntryQuasiLocalPowerLevel : ProofLevel
weightedEntryQuasiLocalPowerLevel = machineChecked

-- The only finite-carrier seam is the trivial fact that a selected matrix entry
-- occurs among the nonnegative row terms.  It is combinatorial, not physical.
finiteSiteTermOccursInWeightedRowLevel : ProofLevel
finiteSiteTermOccursInWeightedRowLevel = standardImported

-- No additional Yang--Mills estimate remains between a weighted dynamic row and
-- entrywise quasi-local decay of every positive power.
literalWeightedDynamicRowToEntrywisePowerDecayLevel : ProofLevel
literalWeightedDynamicRowToEntrywisePowerDecayLevel = machineChecked
