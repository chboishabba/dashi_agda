module DASHI.Physics.Closure.NSTriadKNBishopNatRootOrderRealizationExact where

------------------------------------------------------------------------
-- CLOSE R519'S CONSTRUCTIVE-REAL ORDER SEAM
--
-- R520 proves the canonical floor-root rational approximants are pointwise
-- monotone in the Nat radicand.  The generic Foundations owner now proves that
-- pointwise order of regular rational approximants realizes the vendored Bishop
-- real order.  Composing them closes the scalar monotonicity receipt requested
-- by R519 without adding a postulate or a new real-number carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import DASHI.Foundations.BishopPointwiseApproximationOrderExact as Order
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Root
import DASHI.Physics.Closure.NSTriadKNBishopNatRootCriticalMultiplierBoundaryRound519Exact as R519
import DASHI.Physics.Closure.NSTriadKNBishopNatRootApproximationMonotonicityRound520Exact as R520

canonicalNatRootMonotonicityClosed : R519.CanonicalNatRootMonotonicity
canonicalNatRootMonotonicityClosed = record
  { R519.monotone = λ {m} {n} m≤n →
      Order.pointwiseApproximationOrderRealizesBishopOrder
        (Root.canonicalRegularApproximation m)
        (Root.canonicalRegularApproximation n)
        (λ precision →
          R520.canonicalFloorApproximationMonotone
            {left = m} {right = n} {precision = precision} m≤n)
  }

modewiseCriticalMultiplierComparisonClosed :
  ∀ {lowerSquared physicalSquared upperSquared : Nat} →
  lowerSquared ≤ physicalSquared →
  physicalSquared ≤ upperSquared →
  R519.ModewiseCriticalMultiplierComparison
    lowerSquared physicalSquared upperSquared
modewiseCriticalMultiplierComparisonClosed =
  R519.monotonicityLiftsSquaredComparison canonicalNatRootMonotonicityClosed

bishopNatRootMonotonicityNowClosed : Bool
bishopNatRootMonotonicityNowClosed = true

modewiseCriticalMultiplierComparisonNowClosed : Bool
modewiseCriticalMultiplierComparisonNowClosed = true

introducesNavierStokesCancellationEstimate : Bool
introducesNavierStokesCancellationEstimate = false

clayPromotion : Bool
clayPromotion = false

bishopNatRootMonotonicityNowClosedIsTrue :
  bishopNatRootMonotonicityNowClosed ≡ true
bishopNatRootMonotonicityNowClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
