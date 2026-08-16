module DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaHistoryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger Dashen and David J. Gross,
-- "Relationship between Lattice and Continuum Definitions of the Gauge-Theory
-- Coupling", Physical Review D 23 (1981), 2340--2344.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- DASHI CONTRIBUTION
--
-- Assemble the per-step finite-lattice Gaussian/quartic estimates into the
-- repository's actual `FiniteLatticeBetaSplit` on one source-normalized
-- coupling trajectory.  This is the bridge between the literal plaquette beta
-- calculation and the already-closed UV-history propagation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaEstimateExact as Estimate

record FiniteLatticeBetaHistoryEstimate
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    estimateAt : Nat → Estimate.FiniteLatticeBetaEstimate

    betaIsTrajectory : ∀ step →
      Estimate.beta (estimateAt step) ≡ Flow.beta trajectory (suc step)

    uniformGaussianLower uniformGaussianUpper : ℚ
    uniformGaussianLowerNonnegative : 0ℚ ≤ uniformGaussianLower

    zLowerIsUniform : ∀ step →
      Estimate.zLower (estimateAt step) ≡ uniformGaussianLower

    gaussianUpper : ∀ step →
      Estimate.betaZ (estimateAt step) ≤ uniformGaussianUpper

open FiniteLatticeBetaHistoryEstimate public

historyBetaZ :
  ∀ {trajectory} → FiniteLatticeBetaHistoryEstimate trajectory → Nat → ℚ
historyBetaZ dataSet step = Estimate.betaZ (estimateAt dataSet step)

historyBetaInt :
  ∀ {trajectory} → FiniteLatticeBetaHistoryEstimate trajectory → Nat → ℚ
historyBetaInt dataSet step = Estimate.betaInt (estimateAt dataSet step)

historySplitExact :
  ∀ {trajectory} (dataSet : FiniteLatticeBetaHistoryEstimate trajectory) step →
  Flow.beta trajectory (suc step)
  ≡ historyBetaZ dataSet step + historyBetaInt dataSet step
historySplitExact dataSet step =
  trans
    (sym (betaIsTrajectory dataSet step))
    (Estimate.betaSplitExact (estimateAt dataSet step))

historyGaussianLower :
  ∀ {trajectory} (dataSet : FiniteLatticeBetaHistoryEstimate trajectory) step →
  uniformGaussianLower dataSet ≤ historyBetaZ dataSet step
historyGaussianLower dataSet step =
  subst
    (λ lower → lower ≤ historyBetaZ dataSet step)
    (zLowerIsUniform dataSet step)
    (Estimate.gaussianLower (estimateAt dataSet step))

estimateHalfIsSplitHalf : ∀ value →
  Estimate.half * value ≡ Split.half value
estimateHalfIsSplitHalf value = ℚRing.solve-∀ value

historyInteractionLower :
  ∀ {trajectory} (dataSet : FiniteLatticeBetaHistoryEstimate trajectory) step →
  0ℚ - Split.half (uniformGaussianLower dataSet)
  ≤ historyBetaInt dataSet step
historyInteractionLower dataSet step =
  let
    estimate = estimateAt dataSet step
    atEstimateLower :
      0ℚ - Split.half (Estimate.zLower estimate)
      ≤ Estimate.betaInt estimate
    atEstimateLower =
      subst
        (λ coefficient → 0ℚ - coefficient ≤ Estimate.betaInt estimate)
        (estimateHalfIsSplitHalf (Estimate.zLower estimate))
        (Estimate.interactionSignedLower estimate)
  in
  subst
    (λ lower → 0ℚ - Split.half lower ≤ historyBetaInt dataSet step)
    (zLowerIsUniform dataSet step)
    atEstimateLower

historyInteractionUpper :
  ∀ {trajectory} (dataSet : FiniteLatticeBetaHistoryEstimate trajectory) step →
  historyBetaInt dataSet step
  ≤ Split.half (uniformGaussianLower dataSet)
historyInteractionUpper dataSet step =
  let
    estimate = estimateAt dataSet step
    atEstimateUpper :
      Estimate.betaInt estimate
      ≤ Split.half (Estimate.zLower estimate)
    atEstimateUpper =
      subst
        (λ coefficient → Estimate.betaInt estimate ≤ coefficient)
        (estimateHalfIsSplitHalf (Estimate.zLower estimate))
        (Estimate.interactionSignedUpper estimate)
  in
  subst
    (λ upper → historyBetaInt dataSet step ≤ Split.half upper)
    (zLowerIsUniform dataSet step)
    atEstimateUpper

finiteEstimatesGiveRepositoryBetaSplit :
  ∀ {trajectory} →
  FiniteLatticeBetaHistoryEstimate trajectory →
  Split.FiniteLatticeBetaSplit trajectory
finiteEstimatesGiveRepositoryBetaSplit dataSet = record
  { Split.FiniteLatticeBetaSplit.betaZ = historyBetaZ dataSet
  ; Split.FiniteLatticeBetaSplit.betaInt = historyBetaInt dataSet
  ; Split.FiniteLatticeBetaSplit.splitExact = historySplitExact dataSet
  ; Split.FiniteLatticeBetaSplit.gaussianLower = uniformGaussianLower dataSet
  ; Split.FiniteLatticeBetaSplit.gaussianUpper = uniformGaussianUpper dataSet
  ; Split.FiniteLatticeBetaSplit.gaussianLowerNonnegative =
      uniformGaussianLowerNonnegative dataSet
  ; Split.FiniteLatticeBetaSplit.betaZLower = historyGaussianLower dataSet
  ; Split.FiniteLatticeBetaSplit.betaZUpper = gaussianUpper dataSet
  ; Split.FiniteLatticeBetaSplit.interactionLower = historyInteractionLower dataSet
  ; Split.FiniteLatticeBetaSplit.interactionUpper = historyInteractionUpper dataSet
  }

ym4FiniteLatticeBetaHistoryAssemblyLevel : ProofLevel
ym4FiniteLatticeBetaHistoryAssemblyLevel = machineChecked
