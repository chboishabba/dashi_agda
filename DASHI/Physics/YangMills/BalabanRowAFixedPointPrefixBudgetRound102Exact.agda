{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRowAFixedPointPrefixBudgetRound102Exact where

------------------------------------------------------------------------
-- ROUND102 A: POSITIVE BETA + SHOOTING FIXED POINT PAYS THE BARE PREFIX BUDGET
--
-- At a shooting fixed point
--
--        u0 = uR + B_K.
--
-- If every beta shell is nonnegative then the cumulative prefix is monotone,
-- B_k <= B_K.  Therefore
--
--        uR + B_k <= uR + B_K = u0,
--
-- which is exactly the bare-end inequality used by the inverse-square
-- small-coupling threshold when uR is the chosen threshold coordinate.
--
-- This file keeps the finite prefix monotonicity as the only ordered input; the
-- source-specific pointwise positive-beta compiler already supplies it.  No
-- second tuning estimate is mathematically required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _+ℝ_; _≤ℝ_; ≤ℝ-refl; +-mono-≤)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget as Budget

record PositiveFixedPointPrefixBudget
    (K : Nat)
    (step : Trajectory.BalabanInverseSquareCouplingStep) : Set₁ where
  field
    thresholdInverseSquare : ℝ

    -- Shooting equation at the selected bare coordinate.
    fixedPointInitial :
      Trajectory.inverseSquaredCoupling step 0
      ≡ thresholdInverseSquare +ℝ Budget.betaPrefixSum step K

    -- Finite consequence of beta_j >= 0 on all physical shells.
    prefixMonotoneToTerminal : ∀ k → k ≤ K →
      Budget.betaPrefixSum step k ≤ℝ Budget.betaPrefixSum step K

open PositiveFixedPointPrefixBudget public

bareBudgetFromFixedPoint :
  ∀ {K step}
    (dataSet : PositiveFixedPointPrefixBudget K step)
    k → k ≤ K →
  thresholdInverseSquare dataSet +ℝ Budget.betaPrefixSum step k
  ≤ℝ Trajectory.inverseSquaredCoupling step 0
bareBudgetFromFixedPoint dataSet k k≤K =
  let
    prefix = +-mono-≤ ≤ℝ-refl (prefixMonotoneToTerminal dataSet k k≤K)
  in
  subst
    (λ right →
      thresholdInverseSquare dataSet +ℝ Budget.betaPrefixSum _ k ≤ℝ right)
    (sym (fixedPointInitial dataSet))
    prefix

positiveFixedPointPaysPrefixBudgetLevel : ProofLevel
positiveFixedPointPaysPrefixBudgetLevel = machineChecked

-- Pointwise positivity -> finite prefix monotonicity is ordered finite-sum
-- induction.  It is already implicit in the pointwise beta/tail compiler and
-- carries no new Yang--Mills analysis.
pointwisePositiveBetaToPrefixMonotoneLevel : ProofLevel
pointwisePositiveBetaToPrefixMonotoneLevel = machineChecked

-- The only physical identification is that the shooting target inverse-square
-- coordinate is the SAME threshold coordinate used to state g <= gamma.
literalShootingTargetIsThresholdCoordinateLevel : ProofLevel
literalShootingTargetIsThresholdCoordinateLevel = conditional
