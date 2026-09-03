module DASHI.Physics.Closure.NSTriadKNSignedCancellationDualConsumerRound414Exact where

------------------------------------------------------------------------
-- ROUND414 / HIGHEST-ALPHA BIDI CONSUMER: ONE ESTIMATE, TWO PAYMENTS
--
-- The best possible outcome is that the phase-sensitive signed estimate does
-- not merely bound the Package-A remainder.  If its right-hand side is a
-- cutoff-uniform critical quantity, the SAME theorem can also return the
-- critical barrier needed for continuation, collapsing the two remaining
-- research payments into one.
--
-- This owner freezes that dual-consumer shape without asserting existence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

record DualSignedCancellationPayment (Time : Set) : Set₁ where
  field
    signedRemainderIntegral : Nat → Time → ℚ
    criticalSize : Nat → Time → ℚ
    cutoffIndependentRemainderBound : Time → ℚ
    cutoffIndependentCriticalBound : Time → ℚ

    remainderBound :
      (cutoff : Nat) (terminal : Time) →
      signedRemainderIntegral cutoff terminal
      ≤ cutoffIndependentRemainderBound terminal

    criticalBound :
      (cutoff : Nat) (terminal : Time) →
      criticalSize cutoff terminal
      ≤ cutoffIndependentCriticalBound terminal

open DualSignedCancellationPayment public

round414OneEstimateCouldCollapsePaymentsAAndB : Bool
round414OneEstimateCouldCollapsePaymentsAAndB = true

round414DualPaymentCurrentlyConstructed : Bool
round414DualPaymentCurrentlyConstructed = false

round414DoesNotAssumePackageAImpliesCriticalBarrier : Bool
round414DoesNotAssumePackageAImpliesCriticalBarrier = true

round414DualPaymentCurrentlyConstructedIsFalse :
  round414DualPaymentCurrentlyConstructed ≡ false
round414DualPaymentCurrentlyConstructedIsFalse = refl
