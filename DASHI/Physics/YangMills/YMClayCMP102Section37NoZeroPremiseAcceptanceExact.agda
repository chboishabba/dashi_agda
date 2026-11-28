module DASHI.Physics.YangMills.YMClayCMP102Section37NoZeroPremiseAcceptanceExact where

------------------------------------------------------------------------
-- Section37 CMP102 original count-zero scalar Bishop order closed.
-- Every finite count is on SAME original CMP109 Sequence.SeriesOf
-- and original GPrefix; zero count G_0=1<=3 is now source-written.
-- The three positive-count A/B original signed wing order leaves
-- remain the only scalar quantitative assumptions. The interacting
-- Wilson/OS/same-H physical mass-gap problem is separate.
-- Agda 2.9 native safe graph: PENDING, not yet run.
------------------------------------------------------------------------

import Real as R
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.YMClayCMP102OriginalZeroCountOrderClosedExact as Zero
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailToLimitExact as Limit
import DASHI.Physics.YangMills.YMClayCMP102OriginalThreeWingOrderWeldExact as Three
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

originalZeroCountOrderPaid : ∀ X → Limit.OriginalZeroCountOrder X
originalZeroCountOrderPaid = Zero.originalZeroCountOrderClosed

originalSourceScalarZeroFromOnlyThreePositiveWings :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Three.OriginalThreeWingOrder X →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalSourceScalarZeroFromOnlyThreePositiveWings =
  Zero.originalGZeroFromPositiveThreeWings
