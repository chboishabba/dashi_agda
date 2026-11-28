module DASHI.Physics.YangMills.YMClayCMP102OriginalTwoOuterWingsToLimitExact where

------------------------------------------------------------------------
-- Section39 original CMP102 main scalar geometry: of the THREE
-- signed residual wings, middle last-B is no longer an assumption.
--
-- Consumer requires precisely the TWO genuine shifted Cauchy
-- A(c-1) and B(c-2) outer wing source orders, and signed quarter
-- domain. The middle 2X*b_n X^n is now proved from SAME original
-- factorial CMP109 monotonicity and Bishop absolute powers.
--
-- Zero count is already paid in Section37. No assumed original
-- G-prefix cancellation, no separate analytic limit.
-- Native Agda 2.9 --safe acceptance PENDING, and the two actual
-- OUTER shifted Cauchy bounds still need source-native proof.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Real as R
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalThreeWingOrderWeldExact as Three
import DASHI.Physics.YangMills.YMClayCMP102OriginalOmittedBPositiveWingExact as Middle
import DASHI.Physics.YangMills.YMClayCMP102OriginalZeroCountOrderClosedExact as Zero
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

OriginalOuterTwoWings : R.ℝ → Set
OriginalOuterTwoWings X =
  ∀ n →
    R._≤_
      (R.∣ R.- (R._*_ X
        (Tail.originalAWing X (suc n))) ∣)
      (R.pow Half.bishopQuarter (suc n))
    ×
    R._≤_
      (R.∣ R._*_
        (R._*_ X X)
        (Tail.originalBWing X (suc n)) ∣)
      (R.pow Half.bishopQuarter (suc n))

originalThreeWingsFromActualTwoOuter :
  ∀ X →
  (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  OriginalOuterTwoWings X →
  Three.OriginalThreeWingOrder X
originalThreeWingsFromActualTwoOuter X inside outer n =
  proj₁ (outer n) ,
    (Middle.originalOmittedBQuarterWing X inside n ,
      proj₂ (outer n))

-- The exact ORIGINAL represented CMP109 scalar value becomes zero
-- from just the two Cauchy outer wing estimates. The signed
-- omitted B source and c=0 are genuine source-written lemmas.
originalGZeroFromActualTwoOuterWings :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  OriginalOuterTwoWings X →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalGZeroFromActualTwoOuterWings X inside outer =
  Zero.originalGZeroFromPositiveThreeWings X inside
    (originalThreeWingsFromActualTwoOuter X inside outer)
