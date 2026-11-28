module DASHI.Physics.YangMills.YMClayCMP102Section35ThreeWingOrderAcceptanceExact where

------------------------------------------------------------------------
-- Native acceptance root for the *actual* original three scalar
-- Cauchy terms and their Bishop signed absolute-order envelope.
-- All three term majorants remain explicit source obligations:
-- neither polynomial cancellation nor finite numerical checks alone
-- imply the corresponding Bishop real order proofs.
--
-- The old native original represented CMP109 limit is consumed
-- without an extra series or unlicensed physical Wilson promotion.
-- Pinned Agda 2.9 and the real import --safe graph are UNRUN.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.YMClayCMP102OriginalThreeWingOrderWeldExact as Three
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailToLimitExact as Limit
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

originalThreeWingFiniteOrderToOriginalPositiveTail :
  ∀ X → Three.OriginalThreeWingOrder X →
  Limit.OriginalPositiveTailOrder X
originalThreeWingFiniteOrderToOriginalPositiveTail =
  Three.originalPositiveTailFromThreeActualWings

originalActualPositiveThreeWingToRepresentedGZero :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Limit.OriginalZeroCountOrder X →
  Three.OriginalThreeWingOrder X →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalActualPositiveThreeWingToRepresentedGZero =
  Three.originalGZeroFromThreeActualWings
