module DASHI.Physics.YangMills.BalabanSZZWilsonCrossoverTerminalGapExact where

------------------------------------------------------------------------
-- ROUND68: BALABAN UV -> SZZ IR TERMINAL-GAP HANDOFF
--
-- PRIMARY SOURCES
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv:2204.12737.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- SOURCE NORMALIZATION / NEW SYNTHESIS
--
-- DASHI's literal Wilson action is
--
--   S_W = u * sum_p [1 - (1/N) Re Tr U_p],       u = 1/g^2.
--
-- Shen--Zhu--Zhu write their Gibbs exponent as
--
--   exp( N beta * sum_p Re Tr U_p ).
--
-- Dropping the field-independent term in exp(-S_W), equality of the plaquette
-- coefficient gives
--
--   N beta_SZZ = u/N,
--   beta_SZZ   = u/N^2.
--
-- Their d=4 SU(N) Bakry--Emery margin
--
--   K_S = N (1/2 - 24 |beta_SZZ|)
--
-- therefore becomes, for positive u,
--
--   K_W(u) = N/2 - (24/N) u.
--
-- Hence the exact pure-Wilson crossover is u < N^2/48.
--
-- More importantly, an RG effective action is Wilson plus an irrelevant
-- remainder R.  If the Hessian of R costs at most rho in the same quadratic
-- form, then
--
--   Ric - Hess(S_W + R) >= K_W(u) - rho.
--
-- Thus a source-native Balaban trajectory can hand off to the published SZZ
-- strong-coupling functional-inequality theorem as soon as
--
--   N/2 - (24/N) u_n - rho_n > 0.
--
-- This module proves the exact normalization and finite RG crossover algebra.
-- It deliberately does NOT assume that a CMP119/CMP122 effective density is
-- already a Wilson action plus a Hessian-controlled remainder; that same-object
-- analytic theorem remains the physical producer.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

oneHalf twentyFour oneFortyEight : ℚ
oneHalf = + 1 / 2
twentyFour = + 24 / 1
oneFortyEight = + 1 / 48

record RationalRankNormalization : Set where
  field
    rankN inverseRankN : ℚ
    inverseLaw : rankN * inverseRankN ≡ 1ℚ
open RationalRankNormalization public

szzBetaFromInverseCoupling : RationalRankNormalization → ℚ → ℚ
szzBetaFromInverseCoupling rank inverseCoupling =
  inverseCoupling * inverseRankN rank * inverseRankN rank

szzExponentCoefficient : RationalRankNormalization → ℚ → ℚ
szzExponentCoefficient rank inverseCoupling =
  rankN rank * szzBetaFromInverseCoupling rank inverseCoupling

wilsonExponentCoefficient : RationalRankNormalization → ℚ → ℚ
wilsonExponentCoefficient rank inverseCoupling =
  inverseCoupling * inverseRankN rank

wilsonSZZExponentCoefficientExact :
  (rank : RationalRankNormalization) →
  ∀ inverseCoupling →
  szzExponentCoefficient rank inverseCoupling
  ≡ wilsonExponentCoefficient rank inverseCoupling
wilsonSZZExponentCoefficientExact rank inverseCoupling =
  trans
    (ℚRing.solve-∀
      (rankN rank) (inverseRankN rank) inverseCoupling)
    (trans
      (cong
        (λ selected →
          inverseCoupling * inverseRankN rank * selected)
        (inverseLaw rank))
      (ℚRing.solve-∀ inverseCoupling (inverseRankN rank)))

szzWilsonCurvatureMargin : RationalRankNormalization → ℚ → ℚ
szzWilsonCurvatureMargin rank inverseCoupling =
  rankN rank * oneHalf
  - twentyFour * inverseRankN rank * inverseCoupling

szzInverseCouplingThreshold : RationalRankNormalization → ℚ
szzInverseCouplingThreshold rank =
  rankN rank * rankN rank * oneFortyEight

thresholdMarginZero :
  (rank : RationalRankNormalization) →
  szzWilsonCurvatureMargin rank (szzInverseCouplingThreshold rank) ≡ 0ℚ
thresholdMarginZero rank =
  trans
    (ℚRing.solve-∀ (rankN rank) (inverseRankN rank))
    (trans
      (cong
        (λ selected →
          rankN rank * oneHalf
          - rankN rank * oneHalf * selected)
        (inverseLaw rank))
      (ℚRing.solve-∀ (rankN rank)))

perturbedSZZCurvatureMargin :
  RationalRankNormalization → ℚ → ℚ → ℚ
perturbedSZZCurvatureMargin rank inverseCoupling remainderHessianCost =
  szzWilsonCurvatureMargin rank inverseCoupling - remainderHessianCost

record SZZPerturbedTerminalCriterion (rank : RationalRankNormalization) : Set where
  field
    inverseCoupling remainderHessianCost : ℚ
    positiveEffectiveCurvature :
      0ℚ < perturbedSZZCurvatureMargin
        rank inverseCoupling remainderHessianCost
open SZZPerturbedTerminalCriterion public

record CrossoverTarget
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (bounds : Flow.UniformBetaEnclosure trajectory) : Set where
  field
    depth : Nat
    targetInverseCoupling : ℚ
    accumulatedDriftReachesTarget :
      Flow.inverseCoupling trajectory 0 - targetInverseCoupling
      ≤ Sums.natAsRational depth * Flow.betaLower bounds
open CrossoverTarget public

crossoverInverseCouplingAtOrBelowTarget :
  ∀ {trajectory}
    {bounds : Flow.UniformBetaEnclosure trajectory} →
  (target : CrossoverTarget trajectory bounds) →
  Flow.inverseCoupling trajectory (depth target)
  ≤ targetInverseCoupling target
crossoverInverseCouplingAtOrBelowTarget {trajectory} {bounds} target =
  let
    tube = Flow.sourceNormalizedTwoSidedUVTube bounds (depth target)
    lowerDrift = proj₁ tube
    compared :
      Flow.inverseCoupling trajectory 0 - targetInverseCoupling target
      ≤ Flow.inverseCoupling trajectory 0
        - Flow.inverseCoupling trajectory (depth target)
    compared = ℚP.≤-trans
      (accumulatedDriftReachesTarget target)
      lowerDrift

    shifted = ℚP.+-monoˡ-≤
      (- Flow.inverseCoupling trajectory 0) compared

    negativeOrder :
      - targetInverseCoupling target
      ≤ - Flow.inverseCoupling trajectory (depth target)
    negativeOrder =
      subst
        (λ lower →
          lower ≤
          (- Flow.inverseCoupling trajectory 0)
          + (Flow.inverseCoupling trajectory 0
            - Flow.inverseCoupling trajectory (depth target)))
        (ℚRing.solve-∀
          (Flow.inverseCoupling trajectory 0)
          (targetInverseCoupling target))
        (subst
          (λ upper →
            (- Flow.inverseCoupling trajectory 0)
            + (Flow.inverseCoupling trajectory 0
              - targetInverseCoupling target)
            ≤ upper)
          (ℚRing.solve-∀
            (Flow.inverseCoupling trajectory 0)
            (Flow.inverseCoupling trajectory (depth target)))
          shifted)

    reversed = ℚP.neg-mono-≤ negativeOrder
  in
  subst
    (λ lower → lower ≤ targetInverseCoupling target)
    (ℚRing.solve-∀ (Flow.inverseCoupling trajectory (depth target)))
    (subst
      (λ upper →
        - (- Flow.inverseCoupling trajectory (depth target)) ≤ upper)
      (ℚRing.solve-∀ (targetInverseCoupling target))
      reversed)

record BalabanToSZZTerminalHandoff
    (rank : RationalRankNormalization)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (bounds : Flow.UniformBetaEnclosure trajectory) : Set₁ where
  field
    crossover : CrossoverTarget trajectory bounds
    remainderHessianCost : ℚ

    effectiveDensityIsWilsonPlusControlledRemainder : Set

    targetLeavesPositivePerturbedSZZMargin :
      0ℚ < perturbedSZZCurvatureMargin
        rank
        (targetInverseCoupling crossover)
        remainderHessianCost

    actualCrossoverMarginAtLeastTargetMargin :
      perturbedSZZCurvatureMargin
        rank
        (targetInverseCoupling crossover)
        remainderHessianCost
      ≤ perturbedSZZCurvatureMargin
        rank
        (Flow.inverseCoupling trajectory (depth crossover))
        remainderHessianCost

    volumeUniformPoincareAtTerminalScale : Set
    derivativeCommutatorPropagationAtTerminalScale : Set
    exponentialSpatialCovarianceDecayAtTerminalScale : Set
open BalabanToSZZTerminalHandoff public

actualTerminalPerturbedSZZMarginPositive :
  ∀ {rank trajectory bounds}
    (handoff : BalabanToSZZTerminalHandoff rank trajectory bounds) →
  0ℚ < perturbedSZZCurvatureMargin
    rank
    (Flow.inverseCoupling trajectory (depth (crossover handoff)))
    (remainderHessianCost handoff)
actualTerminalPerturbedSZZMarginPositive handoff =
  ℚP.<-≤-trans
    (targetLeavesPositivePerturbedSZZMargin handoff)
    (actualCrossoverMarginAtLeastTargetMargin handoff)

balabanSZZNormalizationBridgeLevel : ProofLevel
balabanSZZNormalizationBridgeLevel = machineChecked

balabanSZZFiniteCrossoverCompilerLevel : ProofLevel
balabanSZZFiniteCrossoverCompilerLevel = machineChecked

balabanSZZPerturbedCurvatureCompilerLevel : ProofLevel
balabanSZZPerturbedCurvatureCompilerLevel = machineChecked

physicalBalabanToSZZSameObjectHandoffLevel : ProofLevel
physicalBalabanToSZZSameObjectHandoffLevel = conditional
