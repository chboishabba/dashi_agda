module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound86Exact where

------------------------------------------------------------------------
-- ROUND86 HIGHEST-ALPHA C4 CUT
--
-- Round84/85 opened the compact-transfer nonlinear pressure share all the way
-- to literal finite-Fourier objects.  Round86 incorporates the two external
-- identifications that are actually useful without mistaking them for the
-- missing estimate.
--
-- C4a / principal packet pressure:
--
--   H - (1/2) tr(H) I
--     = H^D - (1/3) Q I,
--
-- and now, on the velocity pairing itself,
--
--   <v,(H - (1/2)tr(H)I)v>
--     = <v,H^D v> - (1/3) Q |v|^2.
--
-- The local Q term is therefore exact; only the anisotropic H^D work remains
-- nonlocal.  This is the Ohkitani--Kishiba pressure-Hessian split in the DASHI
-- normalization.  It does NOT imply that Q controls H^D.
--
-- C4b / cross-shell low-pressure first adjoint:
--
-- comparable/high pressure legs are already order-zero.  The genuinely low
-- pressure leg lands in the existing Grafakos--Torres/Bony three-function
-- shell programme.  Its three unit-weight Schur sums are already cutoff
-- uniformly bounded by 128/93.  Therefore no new Coifman--Meyer summability
-- package is needed: the one remaining theorem is the literal physical power
-- comparison from the relocated pressure coefficient to the canonical kernel
--
--   (1/4)^j (1/32)^d.
--
-- C4c / advective residual remains independent and cannot be charged to the
-- pressure budget by notation.
--
-- Hence the route-killer C4 is now honestly reduced to three quantitative
-- producers:
--
--   (a) anisotropic principal H^D work bound in dangerous-event currency;
--   (b) literal low-pressure coefficient -> canonical first-adjoint kernel;
--   (c) advective residual bound;
--
-- plus the already-explicit viscous term.  Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPressureEnergyOperatorDeviatoricQRound85Exact as Principal
import DASHI.Physics.Closure.NSTriadKNPressureDNPacketPrincipalTailRound85Exact as PacketTail
import DASHI.Physics.Closure.NSTriadKNRelocatedPressureComparableMultiplierBoundRound85Exact as Comparable
import DASHI.Physics.Closure.NSTriadKNLowPressureFirstAdjointKernelBridgeRound86Exact as LowTail
import DASHI.Physics.Closure.NSTriadKNPressureRelativeGrowthThreeWayRound85Exact as ThreeWay

round86PrincipalPressurePairingLocalNonlocalSplit : Bool
round86PrincipalPressurePairingLocalNonlocalSplit =
  Principal.round85PrincipalPressurePairingSplitsAnisotropicAndLocalQ

round86PressureDNPrincipalCrossShellPartition : Bool
round86PressureDNPrincipalCrossShellPartition =
  PacketTail.round85PressureDNSplitsSelectedPrincipalAndCrossShellTail

round86ComparablePressureRelocationOrderZero : Bool
round86ComparablePressureRelocationOrderZero =
  Comparable.round85ComparablePressureLegIsOrderZero

round86FirstAdjointShellSummabilityClosed : Bool
round86FirstAdjointShellSummabilityClosed =
  LowTail.round86LowPressureFirstAdjointSummabilityNeedsNoNewTheorem

round86LiteralLowPressureCoefficientKernelDomination : Bool
round86LiteralLowPressureCoefficientKernelDomination =
  LowTail.round86LiteralLowPressureCoefficientPowerComparisonConstructed

round86AnisotropicPrincipalPressureDangerBound : Bool
round86AnisotropicPrincipalPressureDangerBound = false

round86AdvectiveResidualDangerBound : Bool
round86AdvectiveResidualDangerBound = false

round86PhysicalCompactTransferRelativeGrowthBridge : Bool
round86PhysicalCompactTransferRelativeGrowthBridge = false

round86ClayPromotion : Bool
round86ClayPromotion = false

round86PrincipalPressurePairingLocalNonlocalSplitIsTrue :
  round86PrincipalPressurePairingLocalNonlocalSplit ≡ true
round86PrincipalPressurePairingLocalNonlocalSplitIsTrue = refl

round86ComparablePressureRelocationOrderZeroIsTrue :
  round86ComparablePressureRelocationOrderZero ≡ true
round86ComparablePressureRelocationOrderZeroIsTrue = refl

round86FirstAdjointShellSummabilityClosedIsTrue :
  round86FirstAdjointShellSummabilityClosed ≡ true
round86FirstAdjointShellSummabilityClosedIsTrue = refl

round86LiteralLowPressureCoefficientKernelDominationIsFalse :
  round86LiteralLowPressureCoefficientKernelDomination ≡ false
round86LiteralLowPressureCoefficientKernelDominationIsFalse = refl

round86PhysicalCompactTransferRelativeGrowthBridgeIsFalse :
  round86PhysicalCompactTransferRelativeGrowthBridge ≡ false
round86PhysicalCompactTransferRelativeGrowthBridgeIsFalse = refl

round86ClayPromotionIsFalse : round86ClayPromotion ≡ false
round86ClayPromotionIsFalse = refl
