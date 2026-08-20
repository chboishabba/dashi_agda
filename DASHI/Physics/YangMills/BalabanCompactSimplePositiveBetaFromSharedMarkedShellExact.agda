module DASHI.Physics.YangMills.BalabanCompactSimplePositiveBetaFromSharedMarkedShellExact where

------------------------------------------------------------------------
-- ROUND83: SHARED MARKED SHELL + UNIVERSAL C_A 11/24 -> POSITIVE FULL BETA
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
-- DASHI CONTRIBUTION
--
-- The compact-simple universal coefficient is already
--
--          b_G = C_A(G) * 11/24 > 0.
--
-- Round83's shared marked analytic shell gives the history response budget
--
--          H_n <= C/2
--
-- with no factor proportional to the number of preceding RG steps.  This file
-- performs the exact ordered-field weld.  If the literal history-dependent
-- coefficient satisfies
--
--          b_G <= beta_n + H_n
--
-- and the shared shell consumes at most half the Gaussian margin,
--
--          C/2 + b_G/2 <= b_G,
--
-- then every full coefficient obeys
--
--          beta_n >= b_G/2 > 0.
--
-- Thus the remaining physical beta job is sharply localized to SAME-OBJECT
-- construction of the constrained Wilson/FP/Haar coefficient and proof that
-- its marked history response is the beta projection of the shared analytic
-- shell.  No separate arbitrary-history accumulation theorem remains.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_)
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

    historyBudgetFitsHalfUniversal :
      StepV.half * Shared.analyticConstant shared
      + StepV.half * Group.groupUniversalCoefficient strict group
      ≤ Group.groupUniversalCoefficient strict group

    fullBetaAboveUniversalMinusHistory : ∀ depth →
      Group.groupUniversalCoefficient strict group
      ≤ fullBeta depth
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
    h = Shared.betaHistoryPartial shared scale volume root depth

    hBound : h ≤ StepV.half * Shared.analyticConstant shared
    hBound = Shared.betaHistoryPartialBelowHalfAnalyticConstant
      shared scale volume root depth

    halfPlusHistoryBelowUniversal : b * StepV.half + h ≤ b
    halfPlusHistoryBelowUniversal =
      let
        raised = ℚP.+-mono-≤ ℚP.≤-refl hBound
      in
      ℚP.≤-trans
        raised
        (subst
          (λ left → left ≤ b)
          (ℚRing.solve-∀ b StepV.half (Shared.analyticConstant shared))
          (historyBudgetFitsHalfUniversal dataSet))

    chained : b * StepV.half + h ≤ fullBeta dataSet depth + h
    chained = ℚP.≤-trans
      halfPlusHistoryBelowUniversal
      (fullBetaAboveUniversalMinusHistory dataSet depth)
  in
  ℚP.+-cancelʳ-≤ h chained

compactSimpleSharedShellPositiveBetaCompilerLevel : ProofLevel
compactSimpleSharedShellPositiveBetaCompilerLevel = machineChecked

-- Existing exact theorem: b_G=C_A*11/24 is positive on the strict
-- compact-simple carrier.
compactSimpleUniversalCoefficientPositivityLevel : ProofLevel
compactSimpleUniversalCoefficientPositivityLevel = machineChecked

-- Physical seam after the compiler: instantiate the literal constrained
-- Wilson + reduced-FP + Haar Ward scalar and prove its history response is the
-- shared marked beta projection.  CMP109's dependence on all preceding
-- couplings is thereby handled without a history-length loss.
literalWilsonFPHaarSharedMarkedBetaIdentificationLevel : ProofLevel
literalWilsonFPHaarSharedMarkedBetaIdentificationLevel = conditional
