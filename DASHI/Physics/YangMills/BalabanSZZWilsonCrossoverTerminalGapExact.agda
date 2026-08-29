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
-- DASHI uses S_W = u sum_p[1-(1/N)ReTr U_p], u=1/g^2, while SZZ use
-- exp(N beta sum_p ReTr U_p).  Ignoring the field-independent Wilson constant,
--
--       beta_SZZ = u/N^2.
--
-- Their d=4 SU(N) margin therefore becomes
--
--       K_W(u) = N/2 - (24/N)u,
--
-- with pure-Wilson crossover u < N^2/48.  For an RG remainder with Hessian
-- cost rho, the robust target is K_W(u)-rho > 0.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (proj₁)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

oneHalf twentyFour oneFortyEight : ℚ
oneHalf = + 1 / 2
twentyFour = + 24 / 1
oneFortyEight = + 1 / 48

record RationalRankNormalization : Set where
  field
    rankN inverseRankN : ℚ
    inverseLaw : rankN * inverseRankN ≡ 1ℚ
    inverseRankNonnegative : 0ℚ ≤ inverseRankN
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
  (rank : RationalRankNormalization) → ∀ inverseCoupling →
  szzExponentCoefficient rank inverseCoupling
  ≡ wilsonExponentCoefficient rank inverseCoupling
wilsonSZZExponentCoefficientExact rank inverseCoupling =
  trans
    (ℚRing.solve-∀ (rankN rank) (inverseRankN rank) inverseCoupling)
    (trans
      (cong
        (λ selected → inverseCoupling * inverseRankN rank * selected)
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
          rankN rank * oneHalf - rankN rank * oneHalf * selected)
        (inverseLaw rank))
      (ℚRing.solve-∀ (rankN rank)))

perturbedSZZCurvatureMargin :
  RationalRankNormalization → ℚ → ℚ → ℚ
perturbedSZZCurvatureMargin rank inverseCoupling remainderHessianCost =
  szzWilsonCurvatureMargin rank inverseCoupling - remainderHessianCost

szzSlopeNonnegative :
  (rank : RationalRankNormalization) →
  0ℚ ≤ twentyFour * inverseRankN rank
szzSlopeNonnegative rank =
  subst
    (λ lower → lower ≤ twentyFour * inverseRankN rank)
    (ℚRing.solve-∀ twentyFour)
    (Norm.scaleNonnegative
      twentyFour
      (ℚP.nonNegative⁻¹ twentyFour)
      (inverseRankNonnegative rank))

perturbedSZZMarginAntitone :
  (rank : RationalRankNormalization) →
  ∀ {actual target remainderCost} →
  actual ≤ target →
  perturbedSZZCurvatureMargin rank target remainderCost
  ≤ perturbedSZZCurvatureMargin rank actual remainderCost
perturbedSZZMarginAntitone rank {actual} {target} {remainderCost} actualBelow =
  let
    slope = twentyFour * inverseRankN rank
    scaled : slope * actual ≤ slope * target
    scaled = Norm.scaleNonnegative slope (szzSlopeNonnegative rank) actualBelow
    negScaled = ℚP.neg-mono-≤ scaled
    translated = ℚP.+-monoˡ-≤
      (rankN rank * oneHalf - remainderCost) negScaled
  in
  subst
    (λ lower →
      lower ≤ perturbedSZZCurvatureMargin rank actual remainderCost)
    (ℚRing.solve-∀
      (rankN rank) (inverseRankN rank) target remainderCost)
    (subst
      (λ upper →
        (rankN rank * oneHalf - remainderCost)
          + (- (slope * target))
        ≤ upper)
      (ℚRing.solve-∀
        (rankN rank) (inverseRankN rank) actual remainderCost)
      translated)

record SZZPerturbedTerminalCriterion (rank : RationalRankNormalization) : Set where
  field
    inverseCoupling remainderHessianCost : ℚ
    positiveEffectiveCurvature :
      0ℚ < perturbedSZZCurvatureMargin rank inverseCoupling remainderHessianCost
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
  ∀ {trajectory} {bounds : Flow.UniformBetaEnclosure trajectory} →
  (target : CrossoverTarget trajectory bounds) →
  Flow.inverseCoupling trajectory (depth target) ≤ targetInverseCoupling target
crossoverInverseCouplingAtOrBelowTarget {trajectory} {bounds} target =
  let
    lowerDrift = proj₁
      (Flow.sourceNormalizedTwoSidedUVTube bounds (depth target))
    compared :
      Flow.inverseCoupling trajectory 0 - targetInverseCoupling target
      ≤ Flow.inverseCoupling trajectory 0
        - Flow.inverseCoupling trajectory (depth target)
    compared = ℚP.≤-trans (accumulatedDriftReachesTarget target) lowerDrift
    shifted = ℚP.+-monoˡ-≤ (- Flow.inverseCoupling trajectory 0) compared
    negativeOrder :
      - targetInverseCoupling target
      ≤ - Flow.inverseCoupling trajectory (depth target)
    negativeOrder =
      subst
        (λ lower → lower ≤
          (- Flow.inverseCoupling trajectory 0)
          + (Flow.inverseCoupling trajectory 0
            - Flow.inverseCoupling trajectory (depth target)))
        (ℚRing.solve-∀
          (Flow.inverseCoupling trajectory 0) (targetInverseCoupling target))
        (subst
          (λ upper →
            (- Flow.inverseCoupling trajectory 0)
            + (Flow.inverseCoupling trajectory 0 - targetInverseCoupling target)
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
      (λ upper → - (- Flow.inverseCoupling trajectory (depth target)) ≤ upper)
      (ℚRing.solve-∀ (targetInverseCoupling target))
      reversed)

record BalabanToSZZTerminalHandoff
    (rank : RationalRankNormalization)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (bounds : Flow.UniformBetaEnclosure trajectory) : Set₁ where
  field
    crossover : CrossoverTarget trajectory bounds
    remainderHessianCost : ℚ

    -- Same-object physical seam: identify the source-native coarse effective
    -- density with Wilson coefficient u_n plus a remainder controlled in Hessian.
    effectiveDensityIsWilsonPlusControlledRemainder : Set

    targetLeavesPositivePerturbedSZZMargin :
      0ℚ < perturbedSZZCurvatureMargin
        rank (targetInverseCoupling crossover) remainderHessianCost

    -- Published consequences are kept source-facing; their application must be
    -- to the same effective measure identified above.
    volumeUniformPoincareAtTerminalScale : Set
    derivativeCommutatorPropagationAtTerminalScale : Set
    exponentialSpatialCovarianceDecayAtTerminalScale : Set
open BalabanToSZZTerminalHandoff public

actualTerminalMarginAtLeastTarget :
  ∀ {rank trajectory bounds}
    (handoff : BalabanToSZZTerminalHandoff rank trajectory bounds) →
  perturbedSZZCurvatureMargin
    rank
    (targetInverseCoupling (crossover handoff))
    (remainderHessianCost handoff)
  ≤ perturbedSZZCurvatureMargin
    rank
    (Flow.inverseCoupling trajectory (depth (crossover handoff)))
    (remainderHessianCost handoff)
actualTerminalMarginAtLeastTarget handoff =
  perturbedSZZMarginAntitone _
    (crossoverInverseCouplingAtOrBelowTarget (crossover handoff))

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
    (actualTerminalMarginAtLeastTarget handoff)

balabanSZZNormalizationBridgeLevel : ProofLevel
balabanSZZNormalizationBridgeLevel = machineChecked

balabanSZZFiniteCrossoverCompilerLevel : ProofLevel
balabanSZZFiniteCrossoverCompilerLevel = machineChecked

balabanSZZPerturbedCurvatureCompilerLevel : ProofLevel
balabanSZZPerturbedCurvatureCompilerLevel = machineChecked

physicalBalabanToSZZSameObjectHandoffLevel : ProofLevel
physicalBalabanToSZZSameObjectHandoffLevel = conditional
