{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityActiveScaleInverseCouplingNoGoExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Foundations.CMP119AntigravityWeakCouplingTraceEnergyNoGoExact as NoGo
import DASHI.Physics.Foundations.CMP119AntigravityLorentzianF2ContinuationExact as Continuation
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History

------------------------------------------------------------------------
-- ACTIVE CMP119 BETA HISTORY -> TRACE-ENERGY NO-GO
--
-- The finite beta history already proves, at every active scale,
--
--   inverseThreshold <= u_k = 1/g_k^2.
--
-- Therefore if the SAME-unit anomaly threshold 2*kappa is below that history
-- threshold, the weak-coupling no-go follows at every active scale.
--
-- The only remaining physical normalization theorem is precisely:
--
--   2*kappa <= inverseThreshold
--
-- on one common coupling convention.
------------------------------------------------------------------------

record ActiveScaleTraceThresholdCertificate
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    (history :
      History.FiniteModeInverseSquareTerminalHistoryData
        trajectory Mode Atom betaData) : Set₁ where
  field
    anomalyMagnitude : ℚ
    anomalyMagnitudeNonnegative : 0ℚ ≤ anomalyMagnitude

    twiceAnomalyBelowHistoryThreshold :
      (1ℚ + 1ℚ) * anomalyMagnitude
      ≤ History.inverseThreshold history

    sameCouplingNormalization : Set
    sameCouplingNormalizationWitness : sameCouplingNormalization

open ActiveScaleTraceThresholdCertificate public

activeScaleTwiceAnomalyBelowInverseCoupling :
  ∀ {trajectory Mode Atom betaData history}
    (certificate :
      ActiveScaleTraceThresholdCertificate
        {trajectory = trajectory}
        {Mode = Mode} {Atom = Atom} {betaData = betaData}
        history)
    scale →
    History.ActiveScale history scale →
  (1ℚ + 1ℚ) * anomalyMagnitude certificate
  ≤ Flow.inverseCoupling trajectory scale
activeScaleTwiceAnomalyBelowInverseCoupling
    {history = history} certificate scale active =
  ℚP.≤-trans
    (twiceAnomalyBelowHistoryThreshold certificate)
    (History.finiteModeTerminalThresholdAtActiveScale
      history scale active)

activeScaleNoGoData :
  ∀ {trajectory Mode Atom betaData history}
    (continuation : Continuation.LorentzianF2ContinuationReceipt)
    (certificate :
      ActiveScaleTraceThresholdCertificate
        {trajectory = trajectory}
        {Mode = Mode} {Atom = Atom} {betaData = betaData}
        history)
    (scale : Nat)
    (active : History.ActiveScale history scale) →
  NoGo.WeakCouplingYMTraceEnergyData
activeScaleNoGoData
    {trajectory = trajectory} {history = history}
    continuation certificate scale active =
  let
    threshold =
      (1ℚ + 1ℚ) * anomalyMagnitude certificate

    inverse =
      Flow.inverseCoupling trajectory scale

    margin =
      inverse - threshold

    marginNN : 0ℚ ≤ margin
    marginNN =
      subst
        (λ value → 0ℚ ≤ value)
        (ℚRing.solve-∀ inverse threshold)
        (ℚP.+-monoʳ-≤
          (- threshold)
          (activeScaleTwiceAnomalyBelowInverseCoupling
            certificate scale active))
  in record
    { NoGo.WeakCouplingYMTraceEnergyData.kappa =
        anomalyMagnitude certificate
    ; NoGo.WeakCouplingYMTraceEnergyData.margin =
        margin
    ; NoGo.WeakCouplingYMTraceEnergyData.electricSquare =
        Continuation.electricSquare continuation
    ; NoGo.WeakCouplingYMTraceEnergyData.magneticSquare =
        Continuation.magneticSquare continuation
    ; NoGo.WeakCouplingYMTraceEnergyData.kappaNonnegative =
        anomalyMagnitudeNonnegative certificate
    ; NoGo.WeakCouplingYMTraceEnergyData.marginNonnegative =
        marginNN
    ; NoGo.WeakCouplingYMTraceEnergyData.electricSquareNonnegative =
        Continuation.electricSquareNonnegative continuation
    ; NoGo.WeakCouplingYMTraceEnergyData.magneticSquareNonnegative =
        Continuation.magneticSquareNonnegative continuation
    }

activeCMP119ScaleTraceAnomalyNoGo :
  ∀ {trajectory Mode Atom betaData history}
    (continuation : Continuation.LorentzianF2ContinuationReceipt)
    (certificate :
      ActiveScaleTraceThresholdCertificate
        {trajectory = trajectory}
        {Mode = Mode} {Atom = Atom} {betaData = betaData}
        history)
    scale →
    (active : History.ActiveScale history scale) →
  0ℚ ≤
  NoGo.activeStress
    (activeScaleNoGoData continuation certificate scale active)
activeCMP119ScaleTraceAnomalyNoGo
    continuation certificate scale active =
  NoGo.activeStressNonnegative
    (activeScaleNoGoData continuation certificate scale active)
