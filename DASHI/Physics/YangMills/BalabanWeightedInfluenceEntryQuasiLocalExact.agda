{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWeightedInfluenceEntryQuasiLocalExact where

------------------------------------------------------------------------
-- ROUND102 C-SPATIAL: WEIGHTED POWER ROW -> ENTRYWISE QUASI-LOCALITY
--
-- From nonnegativity and finite-row membership,
--
--   w(x,y) M^(n+1)(x,y)
--      <= sum_z w(x,z) M^(n+1)(x,z)
--      <= rho^(n+1).
--
-- Thus the existing weighted-row theorem already contains the desired
-- entrywise statement.  For w=(3/2)^distance this is the division-free form of
--
--   M^(n+1)(x,y) <= (3/2)^(-distance(x,y)) rho^(n+1).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (suc)
open import Data.Rational.Base as ℚ using (_*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record WeightedEntryQuasiLocalData (Site : Set) : Set₁ where
  field
    majorant : Weighted.WeightedFiniteInfluenceMajorant Site

    -- Pure finite-sum membership theorem: the selected nonnegative row term is
    -- bounded by the whole finite row sum.  For literal finite-volume site
    -- enumeration this follows by list induction; it carries no YM analysis.
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
      (suc n)
weightedEntryPowerBound dataSet n x y =
  ℚP.≤-trans
    (termBelowRowSum dataSet n x y)
    (Weighted.weightedPowerRowBound (majorant dataSet) n x)

weightedEntryQuasiLocalPowerLevel : ProofLevel
weightedEntryQuasiLocalPowerLevel = machineChecked

finiteSiteTermOccursInWeightedRowLevel : ProofLevel
finiteSiteTermOccursInWeightedRowLevel = standardImported

literalWeightedDynamicRowToEntrywisePowerDecayLevel : ProofLevel
literalWeightedDynamicRowToEntrywisePowerDecayLevel = machineChecked
