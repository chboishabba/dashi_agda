module DASHI.Papers.NavierStokes.TheoremInterfaceRound107Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND107 STATUS
--
-- Round107 sharpens the nonlinear Round105/106 wall using the independent Lean
-- reconstruction of the complete finite Galerkin Waleffe forcing network.
--
-- The positive network forcing is reduced there to one cutoff-uniform
-- Serrin/Wiener expenditure:
--
--   integral A(t)^2 L2(t) H1(t) dt,
--
-- with exact coefficient `3 W` at the forcing consumer.  Agda records the same
-- ordered reduction shape, but does not promote the still-unproved physical
-- arbitrary-data expenditure bound.
--
-- The existing Agda Round39 projected Galerkin energy cancellation is reused;
-- it is not a new obligation.
--
-- Live theorem-sized obligations remain exactly TWO:
--
--   A. physical cutoff-uniform Serrin/Wiener expenditure sufficient for the
--      positive Waleffe network-forcing budget;
--   B. physical critical Sobolev/Simon upgrade on the exact same selected
--      Galerkin family and G12 limit solution.
--
-- No Clay promotion is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound107Exact as R107

round107PaperProjectedGalerkinEnergyCancellationClosed : Bool
round107PaperProjectedGalerkinEnergyCancellationClosed =
  R107.round107ProjectedGalerkinEnergyCancellationClosed

round107PaperSerrinWienerForcingReductionShapeClosed : Bool
round107PaperSerrinWienerForcingReductionShapeClosed =
  R107.round107SerrinWienerForcingReductionShapeClosed

round107PaperPhysicalUniformSerrinWienerExpenditureClosed : Bool
round107PaperPhysicalUniformSerrinWienerExpenditureClosed =
  R107.round107PhysicalUniformSerrinWienerExpenditureClosed

round107PaperPhysicalPositiveNetworkForcingBudgetClosed : Bool
round107PaperPhysicalPositiveNetworkForcingBudgetClosed =
  R107.round107PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed

round107PaperUniformGalerkinCriticalBarrierClosed : Bool
round107PaperUniformGalerkinCriticalBarrierClosed =
  R107.round107UniformGalerkinCriticalBarrierClosed

round107PaperPhysicalCriticalSobolevSimonUpgradeClosed : Bool
round107PaperPhysicalCriticalSobolevSimonUpgradeClosed =
  R107.round107PhysicalCriticalSobolevSimonUpgradeClosed

round107PaperLiveTheoremSizedObligationCount : Nat
round107PaperLiveTheoremSizedObligationCount = 2

round107PaperProjectedGalerkinEnergyCancellationClosedIsTrue :
  round107PaperProjectedGalerkinEnergyCancellationClosed ≡ true
round107PaperProjectedGalerkinEnergyCancellationClosedIsTrue = refl

round107PaperSerrinWienerForcingReductionShapeClosedIsTrue :
  round107PaperSerrinWienerForcingReductionShapeClosed ≡ true
round107PaperSerrinWienerForcingReductionShapeClosedIsTrue = refl

round107PaperPhysicalUniformSerrinWienerExpenditureClosedIsFalse :
  round107PaperPhysicalUniformSerrinWienerExpenditureClosed ≡ false
round107PaperPhysicalUniformSerrinWienerExpenditureClosedIsFalse = refl

round107PaperPhysicalPositiveNetworkForcingBudgetClosedIsFalse :
  round107PaperPhysicalPositiveNetworkForcingBudgetClosed ≡ false
round107PaperPhysicalPositiveNetworkForcingBudgetClosedIsFalse = refl

round107PaperUniformGalerkinCriticalBarrierClosedIsFalse :
  round107PaperUniformGalerkinCriticalBarrierClosed ≡ false
round107PaperUniformGalerkinCriticalBarrierClosedIsFalse = refl

round107PaperPhysicalCriticalSobolevSimonUpgradeClosedIsFalse :
  round107PaperPhysicalCriticalSobolevSimonUpgradeClosed ≡ false
round107PaperPhysicalCriticalSobolevSimonUpgradeClosedIsFalse = refl

round107PaperLiveTheoremSizedObligationCountIsTwo :
  round107PaperLiveTheoremSizedObligationCount ≡ 2
round107PaperLiveTheoremSizedObligationCountIsTwo = refl

round107PaperClayPromotion : Bool
round107PaperClayPromotion = false

round107PaperClayPromotionIsFalse : round107PaperClayPromotion ≡ false
round107PaperClayPromotionIsFalse = refl
