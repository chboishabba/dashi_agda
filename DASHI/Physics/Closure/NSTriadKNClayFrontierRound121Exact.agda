module DASHI.Physics.Closure.NSTriadKNClayFrontierRound121Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorBonySumRound121Exact as BonySum

-- Round121 closes the exact sign-preserving four-way decomposition of the
-- Round120 pure commutator carrier.  The only live nonlinear mathematics is
-- now quantitative: pay the four signed class sums uniformly at H^(1/2).

round121PureExternalCommutatorClosed : Bool
round121PureExternalCommutatorClosed = R120.round120PureQuarticCommutatorPairingClosed

round121SignedFourWayBonySumDecompositionClosed : Bool
round121SignedFourWayBonySumDecompositionClosed =
  BonySum.round121SignedFourWayBonySumDecompositionClosed

round121CellwiseAbsoluteValueRequiredBeforeBonySum : Bool
round121CellwiseAbsoluteValueRequiredBeforeBonySum =
  BonySum.round121CellwiseAbsoluteValueRequiredBeforeBonySum

round121PhysicalClasswiseCriticalCommutatorPaymentClosed : Bool
round121PhysicalClasswiseCriticalCommutatorPaymentClosed =
  BonySum.round121ClasswiseCriticalCommutatorPaymentClosed

round121UniformGalerkinCriticalBarrierClosed : Bool
round121UniformGalerkinCriticalBarrierClosed = false

round121PhysicalCriticalSobolevSimonUpgradeClosed : Bool
round121PhysicalCriticalSobolevSimonUpgradeClosed =
  R120.round120PhysicalCriticalSobolevSimonUpgradeClosed

round121CurrentMathematicalPackageCount : Nat
round121CurrentMathematicalPackageCount = 2

round121CurrentVisibleSubleafCount : Nat
round121CurrentVisibleSubleafCount = 2

round121PureExternalCommutatorClosedIsTrue :
  round121PureExternalCommutatorClosed ≡ true
round121PureExternalCommutatorClosedIsTrue = refl

round121SignedFourWayBonySumDecompositionClosedIsTrue :
  round121SignedFourWayBonySumDecompositionClosed ≡ true
round121SignedFourWayBonySumDecompositionClosedIsTrue = refl

round121CellwiseAbsoluteValueRequiredBeforeBonySumIsFalse :
  round121CellwiseAbsoluteValueRequiredBeforeBonySum ≡ false
round121CellwiseAbsoluteValueRequiredBeforeBonySumIsFalse = refl

round121PhysicalClasswiseCriticalCommutatorPaymentClosedIsFalse :
  round121PhysicalClasswiseCriticalCommutatorPaymentClosed ≡ false
round121PhysicalClasswiseCriticalCommutatorPaymentClosedIsFalse = refl

round121ClayPromotion : Bool
round121ClayPromotion = false

round121ClayPromotionIsFalse : round121ClayPromotion ≡ false
round121ClayPromotionIsFalse = refl
