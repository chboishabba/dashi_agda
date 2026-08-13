module DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: Cauchy--Schwarz inequality; classical result, no DOI applicable.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Couple the two numerical resources that Round 53/54 separates:
-- viscosity reserve and fixed-shift additive correction capacity.  Round 56
-- extracts the exact rational no-go directly from one feasible allocation.
-- If C_* is the HH-bad ceiling and B_* the available soft correction cap, then
-- every feasible rational allocation necessarily obeys
--
--   c_total <= (15/16 - 2 C_*) B_*.
--
-- This is weaker than the real-carrier square-root optimizer, but it is exact,
-- radical-free, and immediately falsifiable on the repository's Q carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_; _<_; _≤_; nonNegative; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)

import DASHI.Physics.Closure.NSTriadKNGlobalEffectiveSoftFloorGateRound51Exact as Global
import DASHI.Physics.Closure.NSTriadKNJointSoftCorrectionBudgetRound54Exact as Joint
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

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

------------------------------------------------------------------------
-- ROUND 56: exact two-resource feasibility region.
------------------------------------------------------------------------

oneSixteenth fifteenSixteenths : ℚ
oneSixteenth = Int.+ 1 / 16
fifteenSixteenths = Int.+ 15 / 16

hardFourClassTax : ℚ
hardFourClassTax =
  Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

hardFourClassTaxIsOneSixteenth : hardFourClassTax ≡ oneSixteenth
hardFourClassTaxIsOneSixteenth = solve []

viscosityReserve : ℚ → ℚ
viscosityReserve hhBadCeiling =
  fifteenSixteenths - Sharp.two * hhBadCeiling

viscosityReserveExpanded :
  ∀ hhBadCeiling →
  viscosityReserve hhBadCeiling
  ≡ 1ℚ - hardFourClassTax - Sharp.two * hhBadCeiling
viscosityReserveExpanded hhBadCeiling =
  solve (hhBadCeiling ∷ Critical.oneSixtyFourth ∷ [])

strictGateForcesSoftEtaBelowReserve :
  ∀ {hhBadCeiling allocation} →
  JointGlobalFeasibility hhBadCeiling allocation →
  Joint.softEtaTotal allocation < viscosityReserve hhBadCeiling
strictGateForcesSoftEtaBelowReserve {hhBadCeiling} {allocation} feasible =
  let
    gate = jointGlobalFeasibilityImpliesStrictViscosityGate feasible
    shift =
      Sharp.two * hhBadCeiling + hardFourClassTax

    shifted :
      Global.globalEffectiveEtaTotal
        hhBadCeiling
        (Joint.epsilonCom allocation)
        (Joint.epsilonKernel allocation)
        (Joint.epsilonHHGood allocation)
        + (- shift)
      < 1ℚ + (- shift)
    shifted = ℚP.+-monoʳ-< (- shift) gate

    leftMeaning :
      Global.globalEffectiveEtaTotal
        hhBadCeiling
        (Joint.epsilonCom allocation)
        (Joint.epsilonKernel allocation)
        (Joint.epsilonHHGood allocation)
        + (- shift)
      ≡ Joint.softEtaTotal allocation
    leftMeaning = solve
      ( hhBadCeiling
      ∷ Joint.epsilonCom allocation
      ∷ Joint.epsilonKernel allocation
      ∷ Joint.epsilonHHGood allocation
      ∷ Critical.oneSixtyFourth
      ∷ [])

    rightMeaning :
      1ℚ + (- shift) ≡ viscosityReserve hhBadCeiling
    rightMeaning =
      subst
        (λ reserve → 1ℚ + (- shift) ≡ reserve)
        (sym (viscosityReserveExpanded hhBadCeiling))
        (solve
          ( hhBadCeiling
          ∷ Critical.oneSixtyFourth
          ∷ []))
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

jointRationalTwoResourceNoGo :
  ∀ {hhBadCeiling allocation}
    (feasible : JointGlobalFeasibility hhBadCeiling allocation) →
  Joint.softNumeratorTotal allocation
  ≤ viscosityReserve hhBadCeiling
      * Joint.bCap (correctionCap feasible)
jointRationalTwoResourceNoGo {hhBadCeiling} {allocation} feasible =
  let
    cap = correctionCap feasible
    etaBelowReserve = strictGateForcesSoftEtaBelowReserve feasible
    scaled :
      Joint.softEtaTotal allocation * Joint.bCap cap
      ≤ viscosityReserve hhBadCeiling * Joint.bCap cap
    scaled =
      let instance capNN = nonNegative (Joint.bCapNonnegative cap)
      in ℚP.*-monoʳ-≤-nonNeg
        (Joint.bCap cap)
        (ℚP.<⇒≤ etaBelowReserve)
  in
  ℚP.≤-trans
    (jointGlobalFeasibilityImpliesYoungProductKillTest feasible)
    scaled

jointRationalTwoResourceNoGoStrictWhenCapPositive :
  ∀ {hhBadCeiling allocation}
    (feasible : JointGlobalFeasibility hhBadCeiling allocation) →
  0ℚ < Joint.bCap (correctionCap feasible) →
  Joint.softNumeratorTotal allocation
  < viscosityReserve hhBadCeiling
      * Joint.bCap (correctionCap feasible)
jointRationalTwoResourceNoGoStrictWhenCapPositive
    {hhBadCeiling} {allocation} feasible capPositive =
  let
    cap = correctionCap feasible
    etaStrict = strictGateForcesSoftEtaBelowReserve feasible
    scaledStrict :
      Joint.softEtaTotal allocation * Joint.bCap cap
      < viscosityReserve hhBadCeiling * Joint.bCap cap
    scaledStrict =
      let instance capPos = positive capPositive
      in ℚP.*-monoˡ-<-pos (Joint.bCap cap) etaStrict
  in
  ℚP.≤-<-trans
    (jointGlobalFeasibilityImpliesYoungProductKillTest feasible)
    scaledStrict

jointFeasibilityUsesOneAllocationForBothBudgets : Bool
jointFeasibilityUsesOneAllocationForBothBudgets = true

fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplit : Bool
fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplit = true

round56RationalTwoResourceNoGoConstructed : Bool
round56RationalTwoResourceNoGoConstructed = true

jointFeasibilityUsesOneAllocationForBothBudgetsIsTrue :
  jointFeasibilityUsesOneAllocationForBothBudgets ≡ true
jointFeasibilityUsesOneAllocationForBothBudgetsIsTrue = refl

fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplitIsTrue :
  fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplit ≡ true
fifteenOverThirtyTwoIsRecoveredOnlyAtZeroSoftSplitIsTrue = refl

round56RationalTwoResourceNoGoConstructedIsTrue :
  round56RationalTwoResourceNoGoConstructed ≡ true
round56RationalTwoResourceNoGoConstructedIsTrue = refl
