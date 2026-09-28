{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109CanonicalSU2FiniteHistoryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaEstimateExact as Estimate
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- FORWARD CMP109 + ONE SU(2) LOG WINDOW -> UNIFORM FINITE HISTORY
------------------------------------------------------------------------

physicalData :
  ∀ {trajectory} →
  Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory →
  Plaquette.PhysicalRunningCouplingData Nat
physicalData = Constructor.asPhysicalRunningCouplingData

record UniformSU2LogWindow
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory) : Set where
  field
    casimirIsSU2 :
      Plaquette.casimirAdjoint
        (Plaquette.oneLoop (physicalData weld))
      ≡ SU2.su2Casimir

    logFloor logCeiling : ℚ
    logFloorNonnegative : 0ℚ ≤ logFloor

    logFloorBelow :
      ∀ step →
      logFloor
      ≤ Plaquette.logBlocking
          (Plaquette.oneLoop (physicalData weld)) step

    logBelowCeiling :
      ∀ step →
      Plaquette.logBlocking
        (Plaquette.oneLoop (physicalData weld)) step
      ≤ logCeiling

open UniformSU2LogWindow public

gaussianFloor :
  ∀ {trajectory weld} →
  UniformSU2LogWindow {trajectory = trajectory} weld → ℚ
gaussianFloor window =
  SU2.gaussianSU2Coefficient * logFloor window

gaussianCeiling :
  ∀ {trajectory weld} →
  UniformSU2LogWindow {trajectory = trajectory} weld → ℚ
gaussianCeiling window =
  SU2.gaussianSU2Coefficient * logCeiling window

gaussianFloorNonnegative :
  ∀ {trajectory weld}
    (window : UniformSU2LogWindow {trajectory = trajectory} weld) →
  0ℚ ≤ gaussianFloor window
gaussianFloorNonnegative window =
  let
    factorNN : 0ℚ ≤ SU2.gaussianSU2Coefficient
    factorNN = ℚP.nonNegative⁻¹ SU2.gaussianSU2Coefficient
  in
  Norm.mulNonnegative factorNN (logFloorNonnegative window)

stepGaussianCertificate :
  ∀ {trajectory weld}
    (window : UniformSU2LogWindow {trajectory = trajectory} weld)
    step →
  SU2.SU2GaussianStepCertificate
    (Plaquette.oneLoop (physicalData weld))
    step
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
  ∀ {trajectory weld}
    (window : UniformSU2LogWindow {trajectory = trajectory} weld)
    step →
  gaussianFloor window
  ≤ Literal.literalBetaZ (physicalData weld) step
gaussianFloorBelowLiteralBetaZ window step =
  SU2.su2GaussianFiniteLatticeLower
    (stepGaussianCertificate window step)

literalBetaZBelowGaussianCeiling :
  ∀ {trajectory weld}
    (window : UniformSU2LogWindow {trajectory = trajectory} weld)
    step →
  Literal.literalBetaZ (physicalData weld) step
  ≤ gaussianCeiling window
literalBetaZBelowGaussianCeiling {weld = weld} window step =
  let
    exact =
      SU2.literalGaussianIsElevenTwelfthsTimesLog
        (stepGaussianCertificate window step)

    factorNN : 0ℚ ≤ SU2.gaussianSU2Coefficient
    factorNN = ℚP.nonNegative⁻¹ SU2.gaussianSU2Coefficient

    scaled =
      Norm.scaleNonnegative
        SU2.gaussianSU2Coefficient
        factorNN
        (logBelowCeiling window step)
  in
  subst
    (λ lower → lower ≤ gaussianCeiling window)
    (sym exact)
    scaled

coefficientCoupling :
  ∀ {trajectory}
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory) →
  Nat → ℚ
coefficientCoupling weld step =
  Plaquette.coupling
    (Plaquette.remainder (physicalData weld))
    step

record LiteralQuarticCoefficientStep
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (window : UniformSU2LogWindow weld)
    (step : Nat) : Set where
  field
    couplingNonnegative :
      0ℚ ≤ coefficientCoupling weld step

    interactionConstant : ℚ
    interactionConstantNonnegative : 0ℚ ≤ interactionConstant

    signedQuarticRemainder :
      ∣ Literal.literalBetaInt (physicalData weld) step ∣
      ≤ interactionConstant
        * Estimate.fourthPower (coefficientCoupling weld step)

    quarticFitsHalfGaussianFloor :
      interactionConstant
        * Estimate.fourthPower (coefficientCoupling weld step)
      ≤ Estimate.half * gaussianFloor window

open LiteralQuarticCoefficientStep public

asLiteralFiniteBetaCertificate :
  ∀ {trajectory weld}
    (window : UniformSU2LogWindow {trajectory = trajectory} weld)
    (step : Nat) →
  LiteralQuarticCoefficientStep weld window step →
  Literal.LiteralFiniteBetaCertificate (physicalData weld) step
asLiteralFiniteBetaCertificate weldWindow step quartic = record
  { Literal.LiteralFiniteBetaCertificate.coupling =
      coefficientCoupling _ step
  ; Literal.LiteralFiniteBetaCertificate.zLower =
      gaussianFloor weldWindow
  ; Literal.LiteralFiniteBetaCertificate.couplingNonnegative =
      couplingNonnegative quartic
  ; Literal.LiteralFiniteBetaCertificate.zLowerNonnegative =
      gaussianFloorNonnegative weldWindow
  ; Literal.LiteralFiniteBetaCertificate.gaussianLower =
      gaussianFloorBelowLiteralBetaZ weldWindow step
  ; Literal.LiteralFiniteBetaCertificate.interactionConstant =
      interactionConstant quartic
  ; Literal.LiteralFiniteBetaCertificate.interactionConstantNonnegative =
      interactionConstantNonnegative quartic
  ; Literal.LiteralFiniteBetaCertificate.signedQuarticRemainder =
      signedQuarticRemainder quartic
  ; Literal.LiteralFiniteBetaCertificate.quarticFitsHalfGaussianGap =
      quarticFitsHalfGaussianFloor quartic
  }

record CMP109CanonicalSU2FiniteHistory
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory) : Set₁ where
  field
    logWindow : UniformSU2LogWindow weld
    quarticAt :
      (step : Nat) →
      LiteralQuarticCoefficientStep weld logWindow step

open CMP109CanonicalSU2FiniteHistory public

asCMP109PlaquetteFiniteHistory :
  ∀ {trajectory weld} →
  CMP109CanonicalSU2FiniteHistory
    {trajectory = trajectory} weld →
  FiniteHistory.CMP109PlaquetteFiniteHistory trajectory weld
asCMP109PlaquetteFiniteHistory source = record
  { FiniteHistory.CMP109PlaquetteFiniteHistory.certificateAt =
      λ step →
        asLiteralFiniteBetaCertificate
          (logWindow source)
          step
          (quarticAt source step)
  ; FiniteHistory.CMP109PlaquetteFiniteHistory.uniformGaussianLower =
      gaussianFloor (logWindow source)
  ; FiniteHistory.CMP109PlaquetteFiniteHistory.uniformGaussianUpper =
      gaussianCeiling (logWindow source)
  ; FiniteHistory.CMP109PlaquetteFiniteHistory.uniformGaussianLowerNonnegative =
      gaussianFloorNonnegative (logWindow source)
  ; FiniteHistory.CMP109PlaquetteFiniteHistory.zLowerIsUniform =
      λ step → refl
  ; FiniteHistory.CMP109PlaquetteFiniteHistory.gaussianUpper =
      literalBetaZBelowGaussianCeiling (logWindow source)
  }

freeCertificateCouplingRequired : Bool
freeCertificateCouplingRequired = false

freeUniformGaussianBoundsRequired : Bool
freeUniformGaussianBoundsRequired = false

freeCertificateCouplingRequiredIsFalse :
  freeCertificateCouplingRequired ≡ false
freeCertificateCouplingRequiredIsFalse = refl

freeUniformGaussianBoundsRequiredIsFalse :
  freeUniformGaussianBoundsRequired ≡ false
freeUniformGaussianBoundsRequiredIsFalse = refl

cmp109CanonicalSU2FiniteHistoryCompilerLevel : ProofLevel
cmp109CanonicalSU2FiniteHistoryCompilerLevel = machineChecked
