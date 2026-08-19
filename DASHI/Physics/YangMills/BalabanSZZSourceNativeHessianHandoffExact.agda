module DASHI.Physics.YangMills.BalabanSZZSourceNativeHessianHandoffExact where

------------------------------------------------------------------------
-- ROUND68: SOURCE-NATIVE BALABAN -> SZZ HESSIAN HANDOFF
--
-- PRIMARY SOURCES
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- This is the non-receipt version of the UV->IR handoff.  At one actual RG
-- depth, the SAME effective density carries a Wilson Hessian plus an irrelevant
-- remainder Hessian.  The Wilson coefficient is definitionally tied to the
-- source-normalized running inverse coupling u_n, and the remainder cost is the
-- number controlled by the unified RG norm.
--
-- A finite beta lower bound reaches a target u_*.  Positivity of
--
--   K_W(u_*) - rho
--
-- then implies positivity at the actual u_n because K_W is antitone in u.
-- The Hessian perturbation theorem converts this scalar margin into a lower
-- bound for Ric-Hess(S_eff) on every tangent vector.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanSZZWilsonCrossoverTerminalGapExact as Cross
import DASHI.Physics.YangMills.BalabanSZZHessianPerturbationExact as Hess

record SourceNativeSZZHessianHandoff
    (Tangent : Set)
    (rank : Cross.RationalRankNormalization)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (bounds : Flow.UniformBetaEnclosure trajectory) : Set₁ where
  field
    crossover : Cross.CrossoverTarget trajectory bounds
    remainderHessianCost : ℚ

    hessianData : Hess.WilsonPlusRemainderHessianData Tangent

    wilsonMarginIsRunningSZZMargin :
      Hess.wilsonMargin hessianData
      ≡ Cross.szzWilsonCurvatureMargin
          rank (Flow.inverseCoupling trajectory (Cross.depth crossover))

    remainderCostIsUnifiedNormCost :
      Hess.remainderCost hessianData ≡ remainderHessianCost

    targetCrossoverMarginPositive :
      0ℚ < Cross.perturbedSZZCurvatureMargin
        rank (Cross.targetInverseCoupling crossover) remainderHessianCost
open SourceNativeSZZHessianHandoff public

actualRunningSZZMarginPositive :
  ∀ {Tangent rank trajectory bounds}
    (dataSet : SourceNativeSZZHessianHandoff Tangent rank trajectory bounds) →
  0ℚ < Cross.perturbedSZZCurvatureMargin
    rank
    (Flow.inverseCoupling trajectory (Cross.depth (crossover dataSet)))
    (remainderHessianCost dataSet)
actualRunningSZZMarginPositive dataSet =
  let
    actualBelowTarget =
      Cross.crossoverInverseCouplingAtOrBelowTarget (crossover dataSet)
    targetBelowActualMargin =
      Cross.perturbedSZZMarginAntitone _ actualBelowTarget
  in
  Data.Rational.Properties.<-≤-trans
    (targetCrossoverMarginPositive dataSet)
    targetBelowActualMargin

sourceNativeEffectiveMarginExact :
  ∀ {Tangent rank trajectory bounds}
    (dataSet : SourceNativeSZZHessianHandoff Tangent rank trajectory bounds) →
  Hess.effectiveBakryEmeryMargin (hessianData dataSet)
  ≡ Cross.perturbedSZZCurvatureMargin
      rank
      (Flow.inverseCoupling trajectory (Cross.depth (crossover dataSet)))
      (remainderHessianCost dataSet)
sourceNativeEffectiveMarginExact dataSet
  rewrite wilsonMarginIsRunningSZZMargin dataSet
        | remainderCostIsUnifiedNormCost dataSet = refl

sourceNativeEffectiveMarginPositive :
  ∀ {Tangent rank trajectory bounds}
    (dataSet : SourceNativeSZZHessianHandoff Tangent rank trajectory bounds) →
  0ℚ < Hess.effectiveBakryEmeryMargin (hessianData dataSet)
sourceNativeEffectiveMarginPositive dataSet
  rewrite sourceNativeEffectiveMarginExact dataSet =
  actualRunningSZZMarginPositive dataSet

sourceNativeEffectiveBakryEmeryLower :
  ∀ {Tangent rank trajectory bounds}
    (dataSet : SourceNativeSZZHessianHandoff Tangent rank trajectory bounds) →
    ∀ v →
  Hess.effectiveBakryEmeryMargin (hessianData dataSet)
    * Hess.quadraticMass (hessianData dataSet) v
  ≤ Hess.ricciForm (hessianData dataSet) v
    - Hess.effectiveHessian (hessianData dataSet) v
sourceNativeEffectiveBakryEmeryLower dataSet =
  Hess.effectiveBakryEmeryLower (hessianData dataSet)

sourceNativeSZZHessianHandoffCompilerLevel : ProofLevel
sourceNativeSZZHessianHandoffCompilerLevel = machineChecked

-- Remaining physical estimate: construct `hessianData` from the literal
-- CMP119/CMP122 effective density and prove its remainder Hessian cost from the
-- same unified norm used for continuum convergence.
physicalSourceNativeSZZHessianHandoffLevel : ProofLevel
physicalSourceNativeSZZHessianHandoffLevel = conditional
