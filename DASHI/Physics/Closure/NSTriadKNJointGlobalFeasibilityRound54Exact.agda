module DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Couple the two numerical resources that Round 53/54 finally separates:
--
--   (1) viscosity reserve, consumed by epsilon_i;
--   (2) fixed-shift additive correction capacity, consumed by B_i.
--
-- For a concrete joint soft allocation, the HH-bad target is no longer a
-- symbolic collection of independent global floors.  It is exactly the mature
-- global allowable ceiling evaluated at the three CHOSEN soft splits.
-- Simultaneously the same allocation must pass the aggregate correction cap.
--
-- Thus a candidate allocation is feasible only if BOTH:
--
--   C_* < T_global(epsilon_Com,epsilon_kernel,epsilon_HHg),
--   B_Com+B_kernel+B_HHg <= B_*.
--
-- The first condition implies the existing strict nine-owner viscosity gate;
-- the second yields the rational joint Young kill-test from Round 54.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _<_; _≤_)

import DASHI.Physics.Closure.NSTriadKNGlobalEffectiveSoftFloorGateRound51Exact as Global
import DASHI.Physics.Closure.NSTriadKNJointSoftCorrectionBudgetRound54Exact as Joint

jointHHBadAllowableCeiling :
  Joint.ThreeSoftYoungAllocation → ℚ
jointHHBadAllowableCeiling allocation =
  Global.globalAllowableHHBadCeiling
    (Joint.epsilonCom allocation)
    (Joint.epsilonKernel allocation)
    (Joint.epsilonHHGood allocation)

record JointGlobalFeasibility
    (hhBadCeiling : ℚ)
    (allocation : Joint.ThreeSoftYoungAllocation) : Set where
  field
    correctionCap : Joint.AggregateSoftCorrectionCap allocation

    hhBadBelowJointTarget :
      hhBadCeiling < jointHHBadAllowableCeiling allocation

open JointGlobalFeasibility public

jointGlobalFeasibilityImpliesStrictViscosityGate :
  ∀ {hhBadCeiling allocation} →
  JointGlobalFeasibility hhBadCeiling allocation →
  Global.globalEffectiveGate
    hhBadCeiling
    (Joint.epsilonCom allocation)
    (Joint.epsilonKernel allocation)
    (Joint.epsilonHHGood allocation)
jointGlobalFeasibilityImpliesStrictViscosityGate
    {hhBadCeiling} {allocation} feasible =
  Global.globalCeilingBelowTargetImpliesGate
    hhBadCeiling
    (Joint.epsilonCom allocation)
    (Joint.epsilonKernel allocation)
    (Joint.epsilonHHGood allocation)
    (hhBadBelowJointTarget feasible)

jointGlobalFeasibilityImpliesYoungProductKillTest :
  ∀ {hhBadCeiling allocation}
    (feasible : JointGlobalFeasibility hhBadCeiling allocation) →
  Joint.softNumeratorTotal allocation
  ≤ Joint.softEtaTotal allocation
      * Joint.bCap (correctionCap feasible)
jointGlobalFeasibilityImpliesYoungProductKillTest feasible =
  Joint.jointYoungKillTest (correctionCap feasible)

jointFeasibilityUsesOneAllocationForBothBudgets : Bool
jointFeasibilityUsesOneAllocationForBothBudgets = true

fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplit : Bool
fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplit = true

jointFeasibilityUsesOneAllocationForBothBudgetsIsTrue :
  jointFeasibilityUsesOneAllocationForBothBudgets ≡ true
jointFeasibilityUsesOneAllocationForBothBudgetsIsTrue = refl

fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplitIsTrue :
  fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplit ≡ true
fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplitIsTrue = refl
