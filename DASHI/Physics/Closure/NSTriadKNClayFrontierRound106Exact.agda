module DASHI.Physics.Closure.NSTriadKNClayFrontierRound106Exact where

------------------------------------------------------------------------
-- ROUND106 / CROSS-ROUTE FRONTIER ALIGNMENT
--
-- This round does not add a third Navier--Stokes closure architecture.  It
-- records the result of reopening the older compact-Gamma / near-far /
-- integrated-expenditure / Aubin--Lions stack against the later literal
-- physical triad development.
--
-- RETAINED SUBSTRATE
--
-- The repository already owns theorem-bearing reductions for:
--
--   * near-triad paraproduct absorption;
--   * far-low commutator / multiplier control;
--   * far-high Sobolev / geometric tail control;
--   * integrated expenditure assembly;
--   * concrete Aubin--Lions / nonlinear-limit witness interfaces.
--
-- Those modules remain valid reusable substrate.  Their existence does NOT
-- mean that every real-analysis field in their records is inhabited for the
-- official arbitrary-data Navier--Stokes carrier.
--
-- CURRENT CANONICAL PHYSICAL FRONTIER
--
-- Round105 is strictly later in the physical top-down descent.  It has already
-- reduced the nonlinear discovery lane to the literal Waleffe network:
--
--   adverse mixed-helicity production
--     -> phase damping
--     -> global positive-part payment after summation
--     -> positive Waleffe network forcing
--     -> uniform critical barrier
--     -> same-solution critical limit
--     -> Serrin continuation.
--
-- The current theorem-sized countdown therefore remains exactly TWO:
--
--   A. PhysicalWeightedPositiveWaleffeNetworkForcingBudget
--      A cutoff-uniform endpoint bound for the correctly critical-weighted
--      positive network-forcing integral on the complete physical Galerkin
--      network, for arbitrary smooth periodic data.
--
--   B. PhysicalCriticalSobolevSimonUpgrade
--      The three standard critical compactness pieces on the exact selected
--      Galerkin family / G12 limit element:
--        L^(4/3)_t H^(-1/2)_x time regularity,
--        strong L^2_t H^(1/2)_x compactness,
--        critical weak-* lower semicontinuity.
--
-- ROUTE BOUNDARY
--
-- Rebuilding a global Gaussian Calderon--Zygmund pressure estimate, a new
-- compact-Gamma near/far calculus, or a separate ancient-solution Liouville
-- architecture is NOT required by this current Round105/106 route.  Such a
-- route may still be studied independently, but it does not replace either A
-- or B unless it constructs the same final critical barrier for the same
-- limiting solution or rigorously falsifies the Waleffe route.
--
-- No Clay promotion is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

-- Import the retained substrate so this alignment root fails if those owners
-- disappear or are renamed without an explicit migration.
import DASHI.Physics.Closure.NSCompactGammaNearTriadAbsorptionReduction
import DASHI.Physics.Closure.NSCompactGammaRadiusEightFourierReduction
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound105Exact as R105

------------------------------------------------------------------------
-- Exact reuse of the latest physical reductions.
------------------------------------------------------------------------

round106IntegratedAdversePhasePaymentClosed : Bool
round106IntegratedAdversePhasePaymentClosed =
  R105.round105IntegratedAdversePhasePaymentClosed

round106FrontierReducedToPositiveNetworkForcing : Bool
round106FrontierReducedToPositiveNetworkForcing =
  R105.round105FrontierReducedToPositiveNetworkForcing

round106PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed : Bool
round106PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed =
  R105.round105PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed

round106UniformGalerkinCriticalBarrierClosed : Bool
round106UniformGalerkinCriticalBarrierClosed =
  R105.round105UniformGalerkinCriticalBarrierClosed

round106PhysicalCriticalSobolevSimonUpgradeClosed : Bool
round106PhysicalCriticalSobolevSimonUpgradeClosed =
  R105.round105PhysicalCriticalSobolevSimonUpgradeClosed

------------------------------------------------------------------------
-- Cross-route status.  These are deliberately narrow status statements:
-- `false` means "not required by the current Round105 physical route", not
-- "mathematically impossible" and not "delete the older theorem owner".
------------------------------------------------------------------------

round106RebuildCompactGammaNearFarRequired : Bool
round106RebuildCompactGammaNearFarRequired = false

round106GlobalGaussianPressureRouteRequired : Bool
round106GlobalGaussianPressureRouteRequired = false

round106SeparateAncientLiouvilleRouteRequired : Bool
round106SeparateAncientLiouvilleRouteRequired = false

round106CurrentTheoremSizedObligationCount : Nat
round106CurrentTheoremSizedObligationCount = 2

------------------------------------------------------------------------
-- Regression equalities.
------------------------------------------------------------------------

round106IntegratedAdversePhasePaymentClosedIsTrue :
  round106IntegratedAdversePhasePaymentClosed ≡ true
round106IntegratedAdversePhasePaymentClosedIsTrue = refl

round106FrontierReducedToPositiveNetworkForcingIsTrue :
  round106FrontierReducedToPositiveNetworkForcing ≡ true
round106FrontierReducedToPositiveNetworkForcingIsTrue = refl

round106PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosedIsFalse :
  round106PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed ≡ false
round106PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosedIsFalse = refl

round106UniformGalerkinCriticalBarrierClosedIsFalse :
  round106UniformGalerkinCriticalBarrierClosed ≡ false
round106UniformGalerkinCriticalBarrierClosedIsFalse = refl

round106PhysicalCriticalSobolevSimonUpgradeClosedIsFalse :
  round106PhysicalCriticalSobolevSimonUpgradeClosed ≡ false
round106PhysicalCriticalSobolevSimonUpgradeClosedIsFalse = refl

round106RebuildCompactGammaNearFarRequiredIsFalse :
  round106RebuildCompactGammaNearFarRequired ≡ false
round106RebuildCompactGammaNearFarRequiredIsFalse = refl

round106GlobalGaussianPressureRouteRequiredIsFalse :
  round106GlobalGaussianPressureRouteRequired ≡ false
round106GlobalGaussianPressureRouteRequiredIsFalse = refl

round106SeparateAncientLiouvilleRouteRequiredIsFalse :
  round106SeparateAncientLiouvilleRouteRequired ≡ false
round106SeparateAncientLiouvilleRouteRequiredIsFalse = refl

round106CurrentTheoremSizedObligationCountIsTwo :
  round106CurrentTheoremSizedObligationCount ≡ 2
round106CurrentTheoremSizedObligationCountIsTwo = refl

round106ClayPromotion : Bool
round106ClayPromotion = false

round106ClayPromotionIsFalse : round106ClayPromotion ≡ false
round106ClayPromotionIsFalse = refl
