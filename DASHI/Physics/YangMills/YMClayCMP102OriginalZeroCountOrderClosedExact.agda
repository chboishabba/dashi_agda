module DASHI.Physics.YangMills.YMClayCMP102OriginalZeroCountOrderClosedExact where

------------------------------------------------------------------------
-- Section37 source-original CMP102 count-zero order, not an axiom.
-- The ORIGINAL finite-series constructor already proves G_0(X) = 1
-- for ALL signed X. The ORIGINAL geometric envelope has rate_0=3.
-- This file pays the missing real Bishop ABSOLUTE ORDER 1 <= 3.
-- The positive-count Cauchy wing estimate stays a separate real
-- source obligation. No alternate analytic series or physical
-- interacting Wilson claim is introduced.
-- Native pinned Agda 2.9 elaboration pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero)
open import Data.Integer.Base as Z using (+_; +≤+)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Rational.Unnormalised as Q using (0ℚᵘ; 1ℚᵘ; _/_; *≤*)
import Real as R
import RealProperties as P

import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailToLimitExact as Limit
import DASHI.Physics.YangMills.YMClayCMP102OriginalThreeWingOrderWeldExact as Three
import DASHI.Physics.YangMills.YMClayCMP102OriginalGeometricSqueezeReceiverExact as Rate
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half

originalOneNonnegative : R.NonNegative R.1ℝ
originalOneNonnegative =
  P.0≤x⇒nonNegx
    (P.p≤q⇒p⋆≤q⋆
      0ℚᵘ 1ℚᵘ
      (Q.*≤* (Z.+≤+ z≤n)))

originalOneBelowThree : R._≤_ R.1ℝ Rate.three
originalOneBelowThree =
  P.p≤q⇒p⋆≤q⋆
    1ℚᵘ (+ 3 / 1)
    (Q.*≤* (Z.+≤+ (s≤s z≤n)))

originalRateZeroIsThree :
  R._≃_ (Rate.originalGeometricRate zero) Rate.three
originalRateZeroIsThree =
  let open P.ℝ-Solver
  in solve 1
    (λ t → t ⊗ Κ 1ℚᵘ ⊜ t)
    P.≃-refl Rate.three

originalGZeroCountAbsoluteIsOne : ∀ X →
  R._≃_
    (R.∣ R._-_ (Original.originalGPrefix X zero) R.0ℝ ∣)
    R.1ℝ
originalGZeroCountAbsoluteIsOne X =
  P.≃-trans
    (P.∣-∣-cong
      (P.≃-trans
        (P.+-cong
          (Limit.originalGZeroCountIsOne X)
          (P.-‿cong P.≃-refl))
        (let open P.ℝ-Solver
         in solve 0
           (Κ 1ℚᵘ ⊖ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ)
           P.≃-refl)))
    (P.nonNegx⇒∣x∣≃x originalOneNonnegative)

originalRateZeroAbsoluteIsThree :
  R._≃_ (R.∣ Rate.originalGeometricRate zero ∣) Rate.three
originalRateZeroAbsoluteIsThree =
  P.≃-trans
    (P.∣-∣-cong originalRateZeroIsThree)
    (P.nonNegx⇒∣x∣≃x Three.originalThreeNonnegative)

-- No original zero-count premise: use the SAME finite G source.
originalZeroCountOrderClosed : ∀ X → Limit.OriginalZeroCountOrder X
originalZeroCountOrderClosed X =
  P.≤-respˡ-≃
    (originalGZeroCountAbsoluteIsOne X)
    (P.≤-respʳ-≃
      (P.≃-symm originalRateZeroAbsoluteIsThree)
      originalOneBelowThree)

-- The scalar original represented G=0 now consumes ONLY the three
-- positive-count genuine Bishop order leaves, not count-zero order.
originalGZeroFromPositiveThreeWings :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Three.OriginalThreeWingOrder X →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalGZeroFromPositiveThreeWings X inside hthree =
  Three.originalGZeroFromThreeActualWings
    X inside (originalZeroCountOrderClosed X) hthree
