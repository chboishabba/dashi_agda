{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalSU2LiteralHistoryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaEstimateExact as Estimate
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- UNIFORM SU(2) LOG WINDOW -> CANONICAL LITERAL BETA HISTORY
--
-- The literal one-loop producer already fixes
--
--   beta_Z(k) = (11/12) logBlocking(k)
--
-- in SU(2).  Therefore one common rational enclosure
--
--   logFloor <= logBlocking(k) <= logCeiling
--
-- produces the history-uniform Gaussian floor and ceiling automatically:
--
--   gaussianFloor   = (11/12) logFloor
--   gaussianCeiling = (11/12) logCeiling.
--
-- This removes four independently supplied history fields:
--   uniformGaussianLower,
--   uniformGaussianUpper,
--   zLowerIsUniform,
--   gaussianUpper.
------------------------------------------------------------------------

record UniformSU2LogWindow
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat) : Set where
  field
    casimirIsSU2 :
      Plaquette.casimirAdjoint (Plaquette.oneLoop dataSet) ≡ SU2.su2Casimir

    logFloor logCeiling : ℚ

    logFloorNonnegative : 0ℚ ≤ logFloor

    logFloorBelow :
      ∀ step →
      logFloor
      ≤ Plaquette.logBlocking (Plaquette.oneLoop dataSet) (suc step)

    logBelowCeiling :
      ∀ step →
      Plaquette.logBlocking (Plaquette.oneLoop dataSet) (suc step)
      ≤ logCeiling

open UniformSU2LogWindow public

gaussianFloor :
  ∀ {dataSet} → UniformSU2LogWindow dataSet → ℚ
gaussianFloor window =
  SU2.gaussianSU2Coefficient * logFloor window

gaussianCeiling :
  ∀ {dataSet} → UniformSU2LogWindow dataSet → ℚ
gaussianCeiling window =
  SU2.gaussianSU2Coefficient * logCeiling window

gaussianFloorNonnegative :
  ∀ {dataSet} (window : UniformSU2LogWindow dataSet) →
  0ℚ ≤ gaussianFloor window
gaussianFloorNonnegative window =
  ℚP.*-mono-≤
    (ℚP.nonNegative⁻¹ SU2.gaussianSU2Coefficient)
    (logFloorNonnegative window)
    ℚP.≤-refl
    ℚP.≤-refl

stepGaussianCertificate :
  ∀ {dataSet}
    (window : UniformSU2LogWindow dataSet)
    step →
  SU2.SU2GaussianStepCertificate
    (Plaquette.oneLoop dataSet)
    (suc step)
stepGaussianCertificate window step = record
  { SU2.SU2GaussianStepCertificate.casimirIsSU2 =
      casimirIsSU2 window
  ; SU2.SU2GaussianStepCertificate.logFloor =
      logFloor window
  ; SU2.SU2GaussianStepCertificate.logFloorNonnegative =
      logFloorNonnegative window
  ; SU2.SU2GaussianStepCertificate.logStepNonnegative =
      ℚP.≤-trans
        (logFloorNonnegative window)
        (logFloorBelow window step)
  ; SU2.SU2GaussianStepCertificate.logFloorBelowStep =
      logFloorBelow window step
  }

gaussianFloorBelowLiteralBetaZ :
  ∀ {dataSet}
    (window : UniformSU2LogWindow dataSet)
    step →
  gaussianFloor window
  ≤ Literal.literalBetaZ dataSet (suc step)
gaussianFloorBelowLiteralBetaZ window step =
  SU2.su2GaussianFiniteLatticeLower
    (stepGaussianCertificate window step)

literalBetaZBelowGaussianCeiling :
  ∀ {dataSet}
    (window : UniformSU2LogWindow dataSet)
    step →
  Literal.literalBetaZ dataSet (suc step)
  ≤ gaussianCeiling window
literalBetaZBelowGaussianCeiling {dataSet = dataSet} window step =
  let
    oneLoop = Plaquette.oneLoop dataSet
    exact =
      SU2.literalGaussianIsElevenTwelfthsTimesLog
        (stepGaussianCertificate window step)

    scaled =
      Norm.scaleNonnegative
        SU2.gaussianSU2Coefficient
        (ℚP.nonNegative⁻¹ SU2.gaussianSU2Coefficient)
        (logBelowCeiling window step)
  in
  subst
    (λ lower → lower ≤ gaussianCeiling window)
    (sym exact)
    scaled

------------------------------------------------------------------------
-- Only the genuinely non-Gaussian step data remain:
-- the coupling and an absolute quartic enclosure of beta_int.
------------------------------------------------------------------------

record LiteralQuarticStep
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (window : UniformSU2LogWindow dataSet)
    (step : Nat) : Set where
  field
    coupling : ℚ
    couplingNonnegative : 0ℚ ≤ coupling

    interactionConstant : ℚ
    interactionConstantNonnegative : 0ℚ ≤ interactionConstant

    signedQuarticRemainder :
      ∣ Literal.literalBetaInt dataSet (suc step) ∣
      ≤ interactionConstant
        * Estimate.fourthPower
            coupling

    quarticFitsHalfGaussianFloor :
      interactionConstant
        * Estimate.fourthPower
            coupling
      ≤ Estimate.half
        * gaussianFloor window

open LiteralQuarticStep public

asLiteralFiniteBetaCertificate :
  ∀ {dataSet}
    (window : UniformSU2LogWindow dataSet)
    (step : Nat) →
  LiteralQuarticStep dataSet window step →
  Literal.LiteralFiniteBetaCertificate dataSet (suc step)
asLiteralFiniteBetaCertificate window step quartic = record
  { Literal.LiteralFiniteBetaCertificate.coupling =
      coupling quartic
  ; Literal.LiteralFiniteBetaCertificate.zLower =
      gaussianFloor window
  ; Literal.LiteralFiniteBetaCertificate.couplingNonnegative =
      couplingNonnegative quartic
  ; Literal.LiteralFiniteBetaCertificate.zLowerNonnegative =
      gaussianFloorNonnegative window
  ; Literal.LiteralFiniteBetaCertificate.gaussianLower =
      gaussianFloorBelowLiteralBetaZ window step
  ; Literal.LiteralFiniteBetaCertificate.interactionConstant =
      interactionConstant quartic
  ; Literal.LiteralFiniteBetaCertificate.interactionConstantNonnegative =
      interactionConstantNonnegative quartic
  ; Literal.LiteralFiniteBetaCertificate.signedQuarticRemainder =
      signedQuarticRemainder quartic
  ; Literal.LiteralFiniteBetaCertificate.quarticFitsHalfGaussianGap =
      quarticFitsHalfGaussianFloor quartic
  }

record CanonicalSU2LiteralHistory
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence dataSet) : Set₁ where
  field
    logWindow : UniformSU2LogWindow dataSet
    quarticAt :
      (step : Nat) →
      LiteralQuarticStep dataSet logWindow step

open CanonicalSU2LiteralHistory public

asCanonicalLiteralPlaquetteHistory :
  ∀ {dataSet coherence} →
  CanonicalSU2LiteralHistory dataSet coherence →
  Canonical.CanonicalLiteralPlaquetteHistory dataSet coherence
asCanonicalLiteralPlaquetteHistory source = record
  { Canonical.CanonicalLiteralPlaquetteHistory.certificateAt =
      λ step →
        asLiteralFiniteBetaCertificate
          (logWindow source)
          step
          (quarticAt source step)
  ; Canonical.CanonicalLiteralPlaquetteHistory.uniformGaussianLower =
      gaussianFloor (logWindow source)
  ; Canonical.CanonicalLiteralPlaquetteHistory.uniformGaussianUpper =
      gaussianCeiling (logWindow source)
  ; Canonical.CanonicalLiteralPlaquetteHistory.uniformGaussianLowerNonnegative =
      gaussianFloorNonnegative (logWindow source)
  ; Canonical.CanonicalLiteralPlaquetteHistory.zLowerIsUniform =
      λ step → refl
  ; Canonical.CanonicalLiteralPlaquetteHistory.gaussianUpper =
      literalBetaZBelowGaussianCeiling (logWindow source)
  }

uniformGaussianHistoryFieldsIndependent : Bool
uniformGaussianHistoryFieldsIndependent = false

uniformGaussianHistoryFieldsIndependentIsFalse :
  uniformGaussianHistoryFieldsIndependent ≡ false
uniformGaussianHistoryFieldsIndependentIsFalse = refl

canonicalSU2LiteralHistoryCompilerLevel : ProofLevel
canonicalSU2LiteralHistoryCompilerLevel = machineChecked

-- Remaining quantitative source work is now exactly:
--   * one common finite log window;
--   * one absolute quartic interaction enclosure per step.
canonicalSU2LiteralHistorySourceLevel : ProofLevel
canonicalSU2LiteralHistorySourceLevel = conditional
