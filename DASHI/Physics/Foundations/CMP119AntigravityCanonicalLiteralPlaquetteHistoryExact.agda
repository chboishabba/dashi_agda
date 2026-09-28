{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109FiniteHistoryExact as History
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED LITERAL HISTORY CONSTRUCTOR
--
-- There is no free SourceNormalizedCouplingTrajectory.  It is constructed from
-- the literal plaquette inverse coupling and beta coefficient using the single
-- UV-chain coherence theorem.
------------------------------------------------------------------------

record CanonicalLiteralPlaquetteHistory
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence dataSet) : Set₁ where
  field
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

open CanonicalLiteralPlaquetteHistory public

trajectory :
  ∀ {dataSet} →
  Source.LiteralPlaquetteUVChainCoherence dataSet →
  Flow.SourceNormalizedCouplingTrajectory
trajectory {dataSet} =
  Source.canonicalSourceTrajectory dataSet

asLiteralPlaquetteCMP109FiniteHistory :
  ∀ {dataSet coherence} →
  CanonicalLiteralPlaquetteHistory dataSet coherence →
  History.LiteralPlaquetteCMP109FiniteHistory
    dataSet (trajectory coherence)
asLiteralPlaquetteCMP109FiniteHistory
    {dataSet = dataSet} {coherence = coherence} source = record
  { History.LiteralPlaquetteCMP109FiniteHistory.sameObject =
      Source.canonicalTrajectoryAsUVSameObject dataSet coherence
  ; History.LiteralPlaquetteCMP109FiniteHistory.certificateAt =
      certificateAt source
  ; History.LiteralPlaquetteCMP109FiniteHistory.uniformGaussianLower =
      uniformGaussianLower source
  ; History.LiteralPlaquetteCMP109FiniteHistory.uniformGaussianUpper =
      uniformGaussianUpper source
  ; History.LiteralPlaquetteCMP109FiniteHistory.uniformGaussianLowerNonnegative =
      uniformGaussianLowerNonnegative source
  ; History.LiteralPlaquetteCMP109FiniteHistory.zLowerIsUniform =
      zLowerIsUniform source
  ; History.LiteralPlaquetteCMP109FiniteHistory.gaussianUpper =
      gaussianUpper source
  }

canonicalLiteralPlaquetteHistoryCompilerLevel : ProofLevel
canonicalLiteralPlaquetteHistoryCompilerLevel = machineChecked

-- Remaining source inputs at this stage are exactly:
--   UV chain coherence;
--   per-step finite beta certificates;
--   uniform Gaussian lower/upper bounds.
parallelSourceTrajectoryRequired : Agda.Builtin.Bool.Bool
parallelSourceTrajectoryRequired = Agda.Builtin.Bool.false
