{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109FiniteHistoryExact as LiteralHistory
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SOURCE TRAJECTORY + LITERAL COEFFICIENT WELD -> REPOSITORY BETA SPLIT
--
-- No inverse-coupling coordinate weld and no UV-chain theorem is needed on
-- this preferred direction.  They are definitionally fixed by the constructor.
------------------------------------------------------------------------

record CMP109PlaquetteFiniteHistory
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory) : Set₁ where
  field
    certificateAt :
      (step : Nat) →
      Literal.LiteralFiniteBetaCertificate
        (Constructor.asPhysicalRunningCouplingData weld)
        step

    uniformGaussianLower uniformGaussianUpper : ℚ

    uniformGaussianLowerNonnegative :
      0ℚ ≤ uniformGaussianLower

    zLowerIsUniform :
      ∀ step →
      Literal.zLower (certificateAt step)
      ≡ uniformGaussianLower

    gaussianUpper :
      ∀ step →
      Literal.literalBetaZ
        (Constructor.asPhysicalRunningCouplingData weld) step
      ≤ uniformGaussianUpper

open CMP109PlaquetteFiniteHistory public

asLiteralPlaquetteCMP109FiniteHistory :
  ∀ {trajectory weld} →
  CMP109PlaquetteFiniteHistory trajectory weld →
  LiteralHistory.LiteralPlaquetteCMP109FiniteHistory
    (Constructor.asPhysicalRunningCouplingData weld)
    trajectory
asLiteralPlaquetteCMP109FiniteHistory {weld = weld} source = record
  { LiteralHistory.LiteralPlaquetteCMP109FiniteHistory.sameObject =
      Constructor.asLiteralPlaquetteCMP109UVSameObject weld
  ; LiteralHistory.LiteralPlaquetteCMP109FiniteHistory.certificateAt =
      certificateAt source
  ; LiteralHistory.LiteralPlaquetteCMP109FiniteHistory.uniformGaussianLower =
      uniformGaussianLower source
  ; LiteralHistory.LiteralPlaquetteCMP109FiniteHistory.uniformGaussianUpper =
      uniformGaussianUpper source
  ; LiteralHistory.LiteralPlaquetteCMP109FiniteHistory.uniformGaussianLowerNonnegative =
      uniformGaussianLowerNonnegative source
  ; LiteralHistory.LiteralPlaquetteCMP109FiniteHistory.zLowerIsUniform =
      zLowerIsUniform source
  ; LiteralHistory.LiteralPlaquetteCMP109FiniteHistory.gaussianUpper =
      gaussianUpper source
  }

asFiniteLatticeBetaHistoryEstimate :
  ∀ {trajectory weld} →
  CMP109PlaquetteFiniteHistory trajectory weld →
  History.FiniteLatticeBetaHistoryEstimate trajectory
asFiniteLatticeBetaHistoryEstimate source =
  LiteralHistory.asFiniteLatticeBetaHistoryEstimate
    (asLiteralPlaquetteCMP109FiniteHistory source)

repositoryBetaSplit :
  ∀ {trajectory weld} →
  CMP109PlaquetteFiniteHistory trajectory weld →
  Split.FiniteLatticeBetaSplit trajectory
repositoryBetaSplit source =
  History.finiteEstimatesGiveRepositoryBetaSplit
    (asFiniteLatticeBetaHistoryEstimate source)

cmp109PlaquetteFiniteHistoryCompilerLevel : ProofLevel
cmp109PlaquetteFiniteHistoryCompilerLevel = machineChecked

-- Remaining source payments:
--   source beta = literal one-loop + remainder coefficient;
--   literal finite-beta certificates;
--   uniform Gaussian bounds.
cmp109PlaquetteFiniteHistorySourceLevel : ProofLevel
cmp109PlaquetteFiniteHistorySourceLevel = conditional
