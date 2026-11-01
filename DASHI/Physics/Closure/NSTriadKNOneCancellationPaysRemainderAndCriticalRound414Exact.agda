module DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact where

------------------------------------------------------------------------
-- ROUND414 / ONE SIGNED CANCELLATION PAYMENT CAN ALSO PRODUCE THE CRITICAL BAR
--
-- R410 asks for a cutoff-uniform integral bound on the literal R406 weighted
-- remainder.  Independently, the old Round104 signed-critical compiler needs
-- an integrable remainder F_N in
--
--   integratedSignedProduction <= a D_N + F_N.
--
-- The high-alpha BIDI move is to make these the SAME object.  This file sets
-- Round104's F_N definitionally equal to the R406 remainder integral and proves
-- that an R410 cancellation bound plus a cutoff-uniform initial critical bound
-- constructs `UniformSignedCriticalProductionFamily`.
--
-- Thus no second remainder estimate is needed for continuation.  The only
-- remaining physical discovery inside this bridge is the phase-sensitive
-- signed-production estimate with the literal R406 remainder on its RHS.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNSignedTTStarCriticalCancellationTargetRound410Exact as R410
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed

F : C3.RealField _
F = Rational.rationalRealField

module Unified
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf
  module Cancel = R410.Target
    Time initialTime integrateTo DerivativeOf

  literalRemainderIntegral :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  literalRemainderIntegral T R cutoff terminal =
    integrateTo
      (λ time → Flux.At.weightedRemainder T R cutoff time)
      terminal

  record CriticalSliceOnLiteralR406
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (terminal : Time)
      (cutoff : Nat) : Set where
    field
      initialCritical : ℚ
      terminalCritical : ℚ
      criticalDissipation : ℚ
      integratedSignedProduction : ℚ
      viscousCoefficient : ℚ
      absorbedCoefficient : ℚ

      criticalEnergyInequality :
        terminalCritical + viscousCoefficient * criticalDissipation
        ≤ initialCritical + integratedSignedProduction

      signedProductionEstimateByLiteralRemainder :
        integratedSignedProduction
        ≤ absorbedCoefficient * criticalDissipation
          + literalRemainderIntegral T R cutoff terminal

  open CriticalSliceOnLiteralR406 public

  toSignedCriticalSlice :
    ∀ {T R terminal cutoff} →
    CriticalSliceOnLiteralR406 T R terminal cutoff →
    Signed.IntegratedSignedCriticalSlice
  toSignedCriticalSlice {T} {R} {terminal} {cutoff} S = record
    { Signed.initialCritical = initialCritical S
    ; Signed.terminalCritical = terminalCritical S
    ; Signed.criticalDissipation = criticalDissipation S
    ; Signed.integratedSignedProduction = integratedSignedProduction S
    ; Signed.integrableRemainder =
        literalRemainderIntegral T R cutoff terminal
    ; Signed.viscousCoefficient = viscousCoefficient S
    ; Signed.absorbedCoefficient = absorbedCoefficient S
    ; Signed.criticalEnergyInequality = criticalEnergyInequality S
    ; Signed.signedProductionEstimate =
        signedProductionEstimateByLiteralRemainder S
    }

  record UnifiedCancellationCriticalData
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (terminal : Time) : Set₁ where
    field
      cancellation : Cancel.SignedCriticalCancellation T R
      sliceData :
        (cutoff : Nat) →
        CriticalSliceOnLiteralR406 T R terminal cutoff

      uniformInitialCeiling : ℚ
      uniformInitialCritical :
        (cutoff : Nat) →
        initialCritical (sliceData cutoff) ≤ uniformInitialCeiling

  open UnifiedCancellationCriticalData public

  toUniformSignedCriticalProductionFamily :
    ∀ {T R terminal} →
    UnifiedCancellationCriticalData T R terminal →
    Signed.UniformSignedCriticalProductionFamily
  toUniformSignedCriticalProductionFamily {T} {R} {terminal} U = record
    { Signed.Cutoff = Nat
    ; Signed.slice = λ cutoff → toSignedCriticalSlice (sliceData U cutoff)
    ; Signed.uniformCriticalCeiling =
        uniformInitialCeiling U
        + Cancel.cutoffIndependentRemainderBound (cancellation U) terminal
    ; Signed.uniformInitialPlusRemainder = λ cutoff →
        ℚP.+-mono-≤
          (uniformInitialCritical U cutoff)
          (Cancel.signedRemainderBudget
            (cancellation U) cutoff terminal)
    }

  oneCancellationBuildsUniformCriticalBarrier :
    ∀ {T R terminal} →
    (U : UnifiedCancellationCriticalData T R terminal) →
    (cutoff : Nat) →
    let family = toUniformSignedCriticalProductionFamily U in
    Signed.terminalCritical (Signed.slice family cutoff)
      + Signed.retainedViscosity (Signed.slice family cutoff)
          * Signed.criticalDissipation (Signed.slice family cutoff)
    ≤ Signed.uniformCriticalCeiling family
  oneCancellationBuildsUniformCriticalBarrier U cutoff =
    Signed.uniformGalerkinSignedCriticalProduction
      (toUniformSignedCriticalProductionFamily U) cutoff

round414Round104RemainderIsLiteralR406Integral : Bool
round414Round104RemainderIsLiteralR406Integral = true

round414R410BoundReusedAsCriticalRemainderBound : Bool
round414R410BoundReusedAsCriticalRemainderBound = true

round414SecondIndependentRemainderEstimateNeeded : Bool
round414SecondIndependentRemainderEstimateNeeded = false

round414SignedProductionToBarrierAlgebraClosed : Bool
round414SignedProductionToBarrierAlgebraClosed = true

round414RemainingNovelIdentificationIsPhaseSensitiveProductionEstimate : Bool
round414RemainingNovelIdentificationIsPhaseSensitiveProductionEstimate = true

round414SecondIndependentRemainderEstimateNeededIsFalse :
  round414SecondIndependentRemainderEstimateNeeded ≡ false
round414SecondIndependentRemainderEstimateNeededIsFalse = refl

round414SignedProductionToBarrierAlgebraClosedIsTrue :
  round414SignedProductionToBarrierAlgebraClosed ≡ true
round414SignedProductionToBarrierAlgebraClosedIsTrue = refl
