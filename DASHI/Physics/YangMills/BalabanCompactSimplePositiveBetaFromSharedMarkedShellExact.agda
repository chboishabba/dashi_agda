module DASHI.Physics.YangMills.BalabanCompactSimplePositiveBetaFromSharedMarkedShellExact where

------------------------------------------------------------------------
-- ROUND83: LOCAL + IRRELEVANT-MEMORY BUDGETS -> STRICTLY POSITIVE BETA
--
-- PRIMARY SOURCES
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- R. Dashen and D. J. Gross,
-- "Relationship between lattice and continuum definitions of the gauge-theory
-- coupling", Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- ROUND83 CORRECTION
--
-- The full coefficient has two logically distinct residual channels:
--
--   beta_j = b_G + r_local + r_irrelevant-memory,
--
-- where
--
--   b_G = C_A(G) * 11/24 > 0.
--
-- The current/marginal local Bishop remainder MUST NOT be hidden inside an
-- exponentially decaying history tail: Bałaban explicitly says the dependence
-- on g_{j-1} is important.  Only the localized irrelevant/polymer memory is
-- assigned the beta-mark geometric shell.
--
-- This module proves the exact two-budget conclusion.  If
--
--   |r_local| <= R_local,
--   |r_memory| <= C_beta/2,
--
-- and
--
--   b_G/2 + R_local + C_beta/2 <= b_G,
--
-- then
--
--   beta_j >= b_G/2 > 0
--
-- uniformly in the number of preceding RG steps.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanCompactSimpleOneLoopRemainderBudgetExact as Group
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared

record SharedShellCompactSimpleBetaData
    {GaugeGroup Scale Volume Root : Set}
    (strict : Group.StrictCompactSimpleCasimirCarrier GaugeGroup)
    (group : GaugeGroup)
    (shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    (scale : Scale) (volume : Volume) (root : Root) : Set₁ where
  field
    fullBeta : Nat → ℚ

    -- SAME-step / marginal nonlinear remainder.  This is distinct from the
    -- localized irrelevant-memory shell below.
    localRemainderRadius : ℚ
    localRemainderRadiusNonnegative : 0ℚ ≤ localRemainderRadius

    -- Division-free retained-half margin:
    --   b/2 + R_local + C_beta/2 <= b.
    totalRemainderBudgetFitsHalfUniversal :
      (Group.groupUniversalCoefficient strict group * StepV.half
        + localRemainderRadius)
      + StepV.half * Shared.betaAnalyticConstant shared
      ≤ Group.groupUniversalCoefficient strict group

    -- Lower-envelope form of
    --   beta >= b - R_local - H_irrelevant.
    fullBetaAboveUniversalMinusLocalAndMemory : ∀ depth →
      Group.groupUniversalCoefficient strict group
      ≤ (fullBeta depth + localRemainderRadius)
        + Shared.betaHistoryPartial shared scale volume root depth

open SharedShellCompactSimpleBetaData public

fullBetaKeepsHalfUniversal :
  ∀ {GaugeGroup Scale Volume Root}
    {strict : Group.StrictCompactSimpleCasimirCarrier GaugeGroup}
    {group : GaugeGroup}
    {shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    {scale : Scale} {volume : Volume} {root : Root}
    (dataSet :
      SharedShellCompactSimpleBetaData strict group shared scale volume root) →
    ∀ depth →
  Group.groupUniversalCoefficient strict group * StepV.half
  ≤ fullBeta dataSet depth
fullBetaKeepsHalfUniversal
  {strict = strict} {group = group} {shared = shared}
  {scale = scale} {volume = volume} {root = root}
  dataSet depth =
  let
    b = Group.groupUniversalCoefficient strict group
    r = localRemainderRadius dataSet
    h = Shared.betaHistoryPartial shared scale volume root depth

    hBound : h ≤ StepV.half * Shared.betaAnalyticConstant shared
    hBound = Shared.betaHistoryPartialBelowHalfAnalyticConstant
      shared scale volume root depth

    retainedPlusResidualsBelowUniversal :
      (b * StepV.half + r) + h ≤ b
    retainedPlusResidualsBelowUniversal =
      ℚP.≤-trans
        (ℚP.+-mono-≤ ℚP.≤-refl hBound)
        (totalRemainderBudgetFitsHalfUniversal dataSet)

    chained :
      (b * StepV.half + r) + h
      ≤ (fullBeta dataSet depth + r) + h
    chained = ℚP.≤-trans
      retainedPlusResidualsBelowUniversal
      (fullBetaAboveUniversalMinusLocalAndMemory dataSet depth)

    withoutMemory : b * StepV.half + r ≤ fullBeta dataSet depth + r
    withoutMemory = ℚP.+-cancelʳ-≤ h chained
  in
  ℚP.+-cancelʳ-≤ r withoutMemory

halfPositive : 0ℚ < StepV.half
halfPositive = ℚP.positive⁻¹ StepV.half

halfUniversalStrictlyPositive :
  ∀ {GaugeGroup}
    (strict : Group.StrictCompactSimpleCasimirCarrier GaugeGroup)
    group →
  0ℚ < Group.groupUniversalCoefficient strict group * StepV.half
halfUniversalStrictlyPositive strict group =
  let
    b = Group.groupUniversalCoefficient strict group

    instance
      bPositive = positive (Group.groupUniversalCoefficientPositive strict group)

    scaled : b * 0ℚ < b * StepV.half
    scaled = ℚP.*-monoʳ-<-pos b halfPositive
  in
  subst
    (λ left → left < b * StepV.half)
    (ℚRing.solve-∀ b)
    scaled

fullBetaStrictlyPositive :
  ∀ {GaugeGroup Scale Volume Root}
    {strict : Group.StrictCompactSimpleCasimirCarrier GaugeGroup}
    {group : GaugeGroup}
    {shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    {scale : Scale} {volume : Volume} {root : Root}
    (dataSet :
      SharedShellCompactSimpleBetaData strict group shared scale volume root) →
    ∀ depth →
  0ℚ < fullBeta dataSet depth
fullBetaStrictlyPositive {strict = strict} {group = group} dataSet depth =
  ℚP.<-≤-trans
    (halfUniversalStrictlyPositive strict group)
    (fullBetaKeepsHalfUniversal dataSet depth)

compactSimpleTwoChannelPositiveBetaCompilerLevel : ProofLevel
compactSimpleTwoChannelPositiveBetaCompilerLevel = machineChecked

compactSimpleTwoChannelStrictPositiveBetaCompilerLevel : ProofLevel
compactSimpleTwoChannelStrictPositiveBetaCompilerLevel = machineChecked

-- Backward-compatible status names.
compactSimpleSharedShellPositiveBetaCompilerLevel : ProofLevel
compactSimpleSharedShellPositiveBetaCompilerLevel = machineChecked

compactSimpleSharedShellStrictPositiveBetaCompilerLevel : ProofLevel
compactSimpleSharedShellStrictPositiveBetaCompilerLevel = machineChecked

compactSimpleUniversalCoefficientPositivityLevel : ProofLevel
compactSimpleUniversalCoefficientPositivityLevel = machineChecked

-- Physical seams after the compiler:
--   (1) localRemainderRadius: literal same-step Wilson/FP/Haar Bishop remainder;
--   (2) beta mark: only the irrelevant/polymer-memory response at fixed
--       declared marginal data.
literalWilsonFPHaarLocalRemainderLevel : ProofLevel
literalWilsonFPHaarLocalRemainderLevel = conditional

literalWilsonFPHaarIrrelevantMemoryProjectionLevel : ProofLevel
literalWilsonFPHaarIrrelevantMemoryProjectionLevel = conditional
