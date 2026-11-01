module DASHI.Physics.Closure.NSTriadKNSignedTTStarCriticalCancellationTargetRound410Exact where

------------------------------------------------------------------------
-- ROUND410 / HIGHEST-ALPHA PACKAGE-A TARGET: SIGNED TT* CANCELLATION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406

F : C3.RealField _
F = Rational.rationalRealField

module Target
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

  record SignedCriticalCancellation
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      cutoffIndependentRemainderBound : Time → ℚ

      signedRemainderBudget :
        (cutoff : Nat) (terminal : Time) →
        integrateTo
          (λ time → Flux.At.weightedRemainder T R cutoff time)
          terminal
        ≤ cutoffIndependentRemainderBound terminal

  open SignedCriticalCancellation public

round410TargetIsLiteralR406Remainder : Bool
round410TargetIsLiteralR406Remainder = true

round410AllowsWienerL1MajorizationAsFinalPayment : Bool
round410AllowsWienerL1MajorizationAsFinalPayment = false

round410RequiresCutoffIndependentIntegratedBound : Bool
round410RequiresCutoffIndependentIntegratedBound = true

round410SignedPhaseSensitiveCancellationStillOpen : Bool
round410SignedPhaseSensitiveCancellationStillOpen = true

round410TargetIsLiteralR406RemainderIsTrue :
  round410TargetIsLiteralR406Remainder ≡ true
round410TargetIsLiteralR406RemainderIsTrue = refl

round410AllowsWienerL1MajorizationAsFinalPaymentIsFalse :
  round410AllowsWienerL1MajorizationAsFinalPayment ≡ false
round410AllowsWienerL1MajorizationAsFinalPaymentIsFalse = refl
