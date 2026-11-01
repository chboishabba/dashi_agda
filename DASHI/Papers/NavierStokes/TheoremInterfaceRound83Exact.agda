module DASHI.Papers.NavierStokes.TheoremInterfaceRound83Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND83 INTERFACE
--
-- Round82 reduced compact-transfer drift to the exact same-object core
--
--     qdot D - q Ddot.
--
-- Round83 now expands the literal finite Galerkin Navier--Stokes tangent
--
--     F = -nu |k|^2 u + N(u)
--
-- inside both product rules and proves
--
--     qdot = qdot_nu + qdot_N,
--     Ddot = Ddot_nu + Ddot_N,
--
-- hence
--
--     qdot D - q Ddot
--       = (qdot_nu D - q Ddot_nu)
--         + (qdot_N D - q Ddot_N).
--
-- The nonlinear component is constructed directly from the same projected
-- quadratic Fourier nonlinearity used by the selected NS RHS.  This is now the
-- precise C3/C4 target for the existing Round78 pressure/stretching geometry.
-- The physical one-sided/integrated estimate is still open, so the formal
-- 13 substantive + 3 closing cutset and Clay non-promotion remain unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound83Exact as R83

round83LiteralRHSViscousNonlinearSplit : Bool
round83LiteralRHSViscousNonlinearSplit =
  R83.round83LiteralRHSViscousNonlinearSplitConstructed

round83TransferTangentViscousNonlinearSplit : Bool
round83TransferTangentViscousNonlinearSplit =
  R83.round83TransferTangentSplitsViscousNonlinearExactly

round83DissipationTangentViscousNonlinearSplit : Bool
round83DissipationTangentViscousNonlinearSplit =
  R83.round83DissipationTangentSplitsViscousNonlinearExactly

round83RelativeGrowthViscousNonlinearSplit : Bool
round83RelativeGrowthViscousNonlinearSplit =
  R83.round83RelativeGrowthSplitsViscousNonlinearExactly

round83PhysicalPressureEstimateOnNonlinearRelativeGrowth : Bool
round83PhysicalPressureEstimateOnNonlinearRelativeGrowth =
  R83.round83NonlinearPressureRelativeGrowthEstimateConstructed

round83IntegratedDangerOccupationReducerAvailable : Bool
round83IntegratedDangerOccupationReducerAvailable =
  R83.round83IntegratedDangerOccupationReducerConstructed

round83UniformResidenceReducerAvailable : Bool
round83UniformResidenceReducerAvailable =
  R83.round83UniformDangerOccupationUsesExistingResidenceTheorem

round83PhysicalSixThreeGramStillOpen : Bool
round83PhysicalSixThreeGramStillOpen =
  R83.round83PhysicalNormalizedSixThreeGramEstimate

round83PhysicalHHBadCapacityStillOpen : Bool
round83PhysicalHHBadCapacityStillOpen =
  R83.round83PhysicalHHBadCapacityChargeBound

round83PhysicalSoftBoundaryClosureStillOpen : Bool
round83PhysicalSoftBoundaryClosureStillOpen =
  R83.round83PhysicalSoftDataAndBoundaryClosure

round83PhysicalAnnularKernelStillOpen : Bool
round83PhysicalAnnularKernelStillOpen =
  R83.round83PhysicalAnnularMultiplierKernelBound

round83ClayPromotion : Bool
round83ClayPromotion = false

round83RelativeGrowthViscousNonlinearSplitIsTrue :
  round83RelativeGrowthViscousNonlinearSplit ≡ true
round83RelativeGrowthViscousNonlinearSplitIsTrue = refl

round83PhysicalPressureEstimateOnNonlinearRelativeGrowthIsFalse :
  round83PhysicalPressureEstimateOnNonlinearRelativeGrowth ≡ false
round83PhysicalPressureEstimateOnNonlinearRelativeGrowthIsFalse = refl

round83ClayPromotionIsFalse : round83ClayPromotion ≡ false
round83ClayPromotionIsFalse = refl
