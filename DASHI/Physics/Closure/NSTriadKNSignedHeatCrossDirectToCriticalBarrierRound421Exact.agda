module DASHI.Physics.Closure.NSTriadKNSignedHeatCrossDirectToCriticalBarrierRound421Exact where

------------------------------------------------------------------------
-- ROUND421 / ONE PHASE-SENSITIVE PAYMENT -> R410 -> R414 -> CRITICAL BARRIER
--
-- R415 turns a cutoff-uniform bound on the pre-norm signed R299 heat cross into
-- the literal R410 remainder budget.  R414 uses that SAME remainder as
-- Round104's integrable remainder.  This file composes those two owners so the
-- remaining discovery theorem may target one object directly.
--
-- In particular, callers do NOT separately construct an R410 certificate and
-- a Round104 remainder certificate.  The signed heat-cross payment is the sole
-- remainder authority; the remaining physical input is the same-object
-- critical energy/signed-production slice whose remainder is already fixed to
-- R406 by R414.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed

F : C3.RealField _
F = Rational.rationalRealField

module DirectBarrier
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Heat = R415.SignedHeatCross
    Time initialTime integrateTo DerivativeOf
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf

  record SignedHeatCriticalData
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (terminal : Time) : Set₁ where
    field
      heatCrossPayment : Heat.IntegratedSignedHeatCrossPayment T R

      sliceData :
        (cutoff : Nat) →
        Unified.CriticalSliceOnLiteralR406 T R terminal cutoff

      uniformInitialCeiling : ℚ
      uniformInitialCritical :
        (cutoff : Nat) →
        Unified.initialCritical (sliceData cutoff) ≤ uniformInitialCeiling

  open SignedHeatCriticalData public

  asUnifiedCancellationCriticalData :
    ∀ {T R terminal} →
    SignedHeatCriticalData T R terminal →
    Unified.UnifiedCancellationCriticalData T R terminal
  asUnifiedCancellationCriticalData {T} {R} D = record
    { Unified.cancellation =
        Heat.signedHeatCrossBuildsR410 T R (heatCrossPayment D)
    ; Unified.sliceData = sliceData D
    ; Unified.uniformInitialCeiling = uniformInitialCeiling D
    ; Unified.uniformInitialCritical = uniformInitialCritical D
    }

  signedHeatCrossBuildsUniformCriticalFamily :
    ∀ {T R terminal} →
    SignedHeatCriticalData T R terminal →
    Signed.UniformSignedCriticalProductionFamily
  signedHeatCrossBuildsUniformCriticalFamily D =
    Unified.toUniformSignedCriticalProductionFamily
      (asUnifiedCancellationCriticalData D)

  signedHeatCrossBuildsUniformCriticalBarrier :
    ∀ {T R terminal} →
    (D : SignedHeatCriticalData T R terminal) →
    (cutoff : Nat) →
    let family = signedHeatCrossBuildsUniformCriticalFamily D in
    Signed.terminalCritical (Signed.slice family cutoff)
      + Signed.retainedViscosity (Signed.slice family cutoff)
          * Signed.criticalDissipation (Signed.slice family cutoff)
    ≤ Signed.uniformCriticalCeiling family
  signedHeatCrossBuildsUniformCriticalBarrier D cutoff =
    Unified.oneCancellationBuildsUniformCriticalBarrier
      (asUnifiedCancellationCriticalData D) cutoff

round421SeparateR410CertificateRequiredFromCaller : Bool
round421SeparateR410CertificateRequiredFromCaller = false

round421SeparateCriticalRemainderEstimateRequired : Bool
round421SeparateCriticalRemainderEstimateRequired = false

round421OneSignedHeatCrossPaymentFeedsCriticalBarrier : Bool
round421OneSignedHeatCrossPaymentFeedsCriticalBarrier = true

round421RemainingNovelInputIsSameObjectSignedProductionEstimate : Bool
round421RemainingNovelInputIsSameObjectSignedProductionEstimate = true

round421SeparateR410CertificateRequiredFromCallerIsFalse :
  round421SeparateR410CertificateRequiredFromCaller ≡ false
round421SeparateR410CertificateRequiredFromCallerIsFalse = refl

round421OneSignedHeatCrossPaymentFeedsCriticalBarrierIsTrue :
  round421OneSignedHeatCrossPaymentFeedsCriticalBarrier ≡ true
round421OneSignedHeatCrossPaymentFeedsCriticalBarrierIsTrue = refl
