module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound83Exact where

------------------------------------------------------------------------
-- ROUND83 HIGHEST-ALPHA CUTSET
--
-- Round82 made qdot D - q Ddot a literal same-object scalar on the exact
-- finite Galerkin Navier--Stokes tangent.  Round83 now opens that tangent rather
-- than adding another abstract coercivity receipt:
--
--   F = F_nu + F_N
--     = -nu |k|^2 u + N(u),
--
-- and proves, on the same packet carrier,
--
--   qdot = qdot_nu + qdot_N,
--   Ddot = Ddot_nu + Ddot_N,
--
-- hence
--
--   qdot D - q Ddot
--     = (qdot_nu D - q Ddot_nu)
--       + (qdot_N D - q Ddot_N).
--
-- The first component is the literal viscous response.  The second is built
-- from the literal projected quadratic nonlinearity in both the transfer and
-- dissipation product rules and is therefore the correct component on which to
-- seek the Round78 pressure/stretching expenditure.  No sign is fabricated.
--
-- The central C3/C4/C5 producer is consequently narrower:
--
--   pressure-resolved selected-event geometry
--     -> cutoff-uniform control of nonlinearRelativeGrowthCore
--     -> combine with the explicit viscousRelativeGrowthCore
--     -> integrated unabsorbed compact-transfer margin
--     -> existing occupation/replenishment/residence machinery.
--
-- The 13 substantive + 3 closing obligation count is unchanged by this algebra
-- because the physical inequality remains open.  What changed is the object of
-- that inequality: it no longer receives an opaque whole-RHS derivative.
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound82Exact as R82
import DASHI.Physics.Closure.NSTriadKNLiteralRHSRelativeGrowthSplitRound83Exact as Split

round83LiteralRHSViscousNonlinearSplitConstructed : Bool
round83LiteralRHSViscousNonlinearSplitConstructed =
  Split.round83LiteralRHSViscousNonlinearSplitConstructed

round83TransferTangentSplitsViscousNonlinearExactly : Bool
round83TransferTangentSplitsViscousNonlinearExactly =
  Split.round83TransferTangentSplitsViscousNonlinearExactly

round83DissipationTangentSplitsViscousNonlinearExactly : Bool
round83DissipationTangentSplitsViscousNonlinearExactly =
  Split.round83DissipationTangentSplitsViscousNonlinearExactly

round83RelativeGrowthSplitsViscousNonlinearExactly : Bool
round83RelativeGrowthSplitsViscousNonlinearExactly =
  Split.round83RelativeGrowthSplitsViscousNonlinearExactly

round83NonlinearPressureRelativeGrowthEstimateConstructed : Bool
round83NonlinearPressureRelativeGrowthEstimateConstructed =
  Split.round83NonlinearComponentPhysicalPressureEstimateConstructed

round83IntegratedDangerOccupationReducerConstructed : Bool
round83IntegratedDangerOccupationReducerConstructed =
  R82.round82IntegratedDangerOccupationReducerConstructed

round83UniformDangerOccupationUsesExistingResidenceTheorem : Bool
round83UniformDangerOccupationUsesExistingResidenceTheorem =
  R82.round82UniformDangerOccupationUsesExistingResidenceTheorem

round83PhysicalNormalizedSixThreeGramEstimate : Bool
round83PhysicalNormalizedSixThreeGramEstimate =
  R82.round82PhysicalNormalizedSixThreeGramEstimate

round83PhysicalHHBadCapacityChargeBound : Bool
round83PhysicalHHBadCapacityChargeBound =
  R82.round82PhysicalHHBadCapacityChargeBound

round83PhysicalSoftDataAndBoundaryClosure : Bool
round83PhysicalSoftDataAndBoundaryClosure =
  R82.round82PhysicalSoftDataAndBoundaryClosure

round83PhysicalAnnularMultiplierKernelBound : Bool
round83PhysicalAnnularMultiplierKernelBound =
  R82.round82PhysicalAnnularMultiplierKernelBound

round83CriticalRatioBarrier : Bool
round83CriticalRatioBarrier = false

round83ClayPromotion : Bool
round83ClayPromotion = false

round83RelativeGrowthSplitsViscousNonlinearExactlyIsTrue :
  round83RelativeGrowthSplitsViscousNonlinearExactly ≡ true
round83RelativeGrowthSplitsViscousNonlinearExactlyIsTrue = refl

round83NonlinearPressureRelativeGrowthEstimateConstructedIsFalse :
  round83NonlinearPressureRelativeGrowthEstimateConstructed ≡ false
round83NonlinearPressureRelativeGrowthEstimateConstructedIsFalse = refl

round83ClayPromotionIsFalse : round83ClayPromotion ≡ false
round83ClayPromotionIsFalse = refl
