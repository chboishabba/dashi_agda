{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109FiniteHistoryExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as Same
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaEstimateExact as Estimate
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- LITERAL PLAQUETTE CERTIFICATES -> ACTUAL CMP109 FINITE BETA HISTORY
--
-- The step indexing is source-faithful:
--
--   history step k consumes literal producer scale suc k,
--
-- so the literal beta is beta_(k+1), exactly the coefficient appearing in
-- CMP109's source recurrence u_k = u_(k+1) + beta_(k+1).
------------------------------------------------------------------------

record LiteralPlaquetteCMP109FiniteHistory
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    sameObject :
      Same.LiteralPlaquetteCMP109UVSameObject dataSet trajectory

    certificateAt :
      (step : Nat) →
      Literal.LiteralFiniteBetaCertificate dataSet (suc step)

    uniformGaussianLower uniformGaussianUpper : ℚ

    uniformGaussianLowerNonnegative :
      0ℚ ≤ uniformGaussianLower

    zLowerIsUniform :
      ∀ step →
      Literal.zLower (certificateAt step)
      ≡ uniformGaussianLower

    gaussianUpper :
      ∀ step →
      Literal.literalBetaZ dataSet (suc step)
      ≤ uniformGaussianUpper

open LiteralPlaquetteCMP109FiniteHistory public

estimateAt :
  ∀ {dataSet trajectory} →
  LiteralPlaquetteCMP109FiniteHistory dataSet trajectory →
  Nat → Estimate.FiniteLatticeBetaEstimate
estimateAt history step =
  Literal.literalCertificateAsFiniteEstimate
    (certificateAt history step)

betaIsTrajectory :
  ∀ {dataSet trajectory}
    (history : LiteralPlaquetteCMP109FiniteHistory dataSet trajectory)
    step →
  Estimate.beta (estimateAt history step)
  ≡ Flow.beta trajectory (suc step)
betaIsTrajectory history step =
  Same.literalBetaIsSourceBeta
    (sameObject history) step

asFiniteLatticeBetaHistoryEstimate :
  ∀ {dataSet trajectory} →
  LiteralPlaquetteCMP109FiniteHistory dataSet trajectory →
  History.FiniteLatticeBetaHistoryEstimate trajectory
asFiniteLatticeBetaHistoryEstimate history = record
  { History.FiniteLatticeBetaHistoryEstimate.estimateAt =
      estimateAt history
  ; History.FiniteLatticeBetaHistoryEstimate.betaIsTrajectory =
      betaIsTrajectory history
  ; History.FiniteLatticeBetaHistoryEstimate.uniformGaussianLower =
      uniformGaussianLower history
  ; History.FiniteLatticeBetaHistoryEstimate.uniformGaussianUpper =
      uniformGaussianUpper history
  ; History.FiniteLatticeBetaHistoryEstimate.uniformGaussianLowerNonnegative =
      uniformGaussianLowerNonnegative history
  ; History.FiniteLatticeBetaHistoryEstimate.zLowerIsUniform =
      zLowerIsUniform history
  ; History.FiniteLatticeBetaHistoryEstimate.gaussianUpper =
      gaussianUpper history
  }

literalPlaquetteGivesRepositoryBetaSplit :
  ∀ {dataSet trajectory} →
  LiteralPlaquetteCMP109FiniteHistory dataSet trajectory →
  Split.FiniteLatticeBetaSplit trajectory
literalPlaquetteGivesRepositoryBetaSplit history =
  History.finiteEstimatesGiveRepositoryBetaSplit
    (asFiniteLatticeBetaHistoryEstimate history)

literalPlaquetteCMP109FiniteHistoryCompilerLevel : ProofLevel
literalPlaquetteCMP109FiniteHistoryCompilerLevel = machineChecked

-- Remaining source work is now:
--   * inhabit the UV same-object coordinate weld;
--   * provide the per-step literal finite beta certificates;
--   * prove the two uniform Gaussian bounds.
-- No independent betaIsTrajectory field remains.
literalPlaquetteCMP109FiniteHistorySourceLevel : ProofLevel
literalPlaquetteCMP109FiniteHistorySourceLevel = conditional
