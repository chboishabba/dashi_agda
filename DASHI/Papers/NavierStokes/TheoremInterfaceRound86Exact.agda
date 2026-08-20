module DASHI.Papers.NavierStokes.TheoremInterfaceRound86Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND86 INTERFACE
--
-- Round86 does not alter the 13 substantive + 3 closing outer cutset.  It does
-- make the decisive C4 package materially sharper.
--
-- Principal pressure work now has the exact scalar decomposition
--
--   <v,(H - (1/2)tr(H)I)v>
--     = <v,H^D v> - (1/3) Q |v|^2,
--
-- so the Q contribution is a literal local term and the remaining principal
-- difficulty is the anisotropic/deviatoric H^D work.
--
-- For the relocated cross-shell tail, comparable/high pressure legs are
-- order-zero and the existing three-orientation shell Schur programme already
-- has cutoff-uniform mass <= 128/93.  The low-pressure tail is therefore
-- reduced to one concrete coefficient-power comparison against the canonical
-- factorized kernel (1/4)^j (1/32)^d.
--
-- The advective residual remains a separate physical estimate.  Thus C4 is
-- reduced to exactly three quantitative producers: anisotropic principal work,
-- literal low-pressure kernel domination, and advective residual control.
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound86Exact as R86

round86PrincipalPressureLocalNonlocalSplit : Bool
round86PrincipalPressureLocalNonlocalSplit =
  R86.round86PrincipalPressurePairingLocalNonlocalSplit

round86PressurePrincipalTailPartition : Bool
round86PressurePrincipalTailPartition =
  R86.round86PressureDNPrincipalCrossShellPartition

round86ComparablePressureTailOrderZero : Bool
round86ComparablePressureTailOrderZero =
  R86.round86ComparablePressureRelocationOrderZero

round86LowPressureFirstAdjointSummabilityClosed : Bool
round86LowPressureFirstAdjointSummabilityClosed =
  R86.round86FirstAdjointShellSummabilityClosed

round86LowPressurePhysicalKernelBridge : Bool
round86LowPressurePhysicalKernelBridge =
  R86.round86LiteralLowPressureCoefficientKernelDomination

round86AnisotropicPrincipalPressureBound : Bool
round86AnisotropicPrincipalPressureBound =
  R86.round86AnisotropicPrincipalPressureDangerBound

round86AdvectiveResidualBound : Bool
round86AdvectiveResidualBound =
  R86.round86AdvectiveResidualDangerBound

round86PhysicalCompactTransferRelativeGrowthBridge : Bool
round86PhysicalCompactTransferRelativeGrowthBridge =
  R86.round86PhysicalCompactTransferRelativeGrowthBridge

round86ClayPromotion : Bool
round86ClayPromotion = false

round86PrincipalPressureLocalNonlocalSplitIsTrue :
  round86PrincipalPressureLocalNonlocalSplit ≡ true
round86PrincipalPressureLocalNonlocalSplitIsTrue = refl

round86LowPressureFirstAdjointSummabilityClosedIsTrue :
  round86LowPressureFirstAdjointSummabilityClosed ≡ true
round86LowPressureFirstAdjointSummabilityClosedIsTrue = refl

round86LowPressurePhysicalKernelBridgeIsFalse :
  round86LowPressurePhysicalKernelBridge ≡ false
round86LowPressurePhysicalKernelBridgeIsFalse = refl

round86PhysicalCompactTransferRelativeGrowthBridgeIsFalse :
  round86PhysicalCompactTransferRelativeGrowthBridge ≡ false
round86PhysicalCompactTransferRelativeGrowthBridgeIsFalse = refl

round86ClayPromotionIsFalse : round86ClayPromotion ≡ false
round86ClayPromotionIsFalse = refl
