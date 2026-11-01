module DASHI.Physics.Closure.NSTriadKNClayFrontierRound113Exact where

------------------------------------------------------------------------
-- ROUND113 / WEIGHTED CROSS-TRIAD REINDEX FRONTIER
--
-- Round112 attached the ACTUAL three-slot external Waleffe functional to exact
-- self-orbit-removed physical convolution fibres.  Round113 now isolates and
-- proves the algebraic mechanism by which a shared-mode reindexing would turn
-- a weighted cross-triad flux into the mature multiplier-difference/commutator
-- form:
--
--   w_a T_ab + w_b T_ba,
--   T_ba = -T_ab
--       ==> (w_a - w_b) T_ab.
--
-- This is an exact discrete integration-by-parts identity.  It also explains
-- why the reality orbit cannot do the job: Round112 has transfer invariance on
-- the reality pair, which produces a weight SUM rather than a difference.
--
-- The remaining same-object question is therefore no longer vague:
--
-- A113a. PhysicalExternalCrossTriadAntisymmetricReindexWeld
--   Expand the actual weighted external Waleffe residual into quartic
--   cross-triad cells and prove that the relevant shared-mode/output-fibre
--   partner has the opposite transfer, modulo an explicitly isolated boundary
--   or occupation remainder.  If exact antisymmetry fails, the theorem must
--   expose that remainder rather than silently replace it by a commutator.
--
-- A113b. PhysicalExternalResidualCutoffUniformQuantitativePayment
--   Once the physical reindex produces the multiplier difference plus any true
--   remainder, apply the existing far-low/Bony/local analytic machinery with
--   cutoff-independent constants and pay the remainder on the same trajectory.
--
-- B. PhysicalCriticalSobolevSimonUpgrade remains unchanged.
--
-- Clay-sized package count remains TWO.  At the fine level there are three
-- visible subleaves: A113a, A113b, B.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound112Exact as R112
import DASHI.Physics.Closure.NSTriadKNExternalSharedModeWeightedFluxRound113Exact as Flux

round113WeightedAntisymmetricPairMultiplierDifferenceClosed : Bool
round113WeightedAntisymmetricPairMultiplierDifferenceClosed =
  Flux.round113AntisymmetricSharedModePairGivesMultiplierDifference

round113RealitySymmetryAloneGivesMultiplierDifference : Bool
round113RealitySymmetryAloneGivesMultiplierDifference =
  Flux.round113RealitySymmetryAloneGivesMultiplierDifference

round113PhysicalExternalCrossTriadAntisymmetricReindexWeldClosed : Bool
round113PhysicalExternalCrossTriadAntisymmetricReindexWeldClosed =
  Flux.round113PhysicalCrossTriadAntisymmetricReindexWeldClosed

round113PhysicalExternalResidualCutoffUniformQuantitativePaymentClosed : Bool
round113PhysicalExternalResidualCutoffUniformQuantitativePaymentClosed =
  R112.round112PhysicalExternalResidualCutoffUniformQuantitativePaymentClosed

round113PhysicalExternalCrossTriadIntegratedResiduePaymentClosed : Bool
round113PhysicalExternalCrossTriadIntegratedResiduePaymentClosed =
  R112.round112PhysicalExternalCrossTriadIntegratedResiduePaymentClosed

round113AgdaPhysicalThreeSlotInternalPaymentPortClosed : Bool
round113AgdaPhysicalThreeSlotInternalPaymentPortClosed =
  R112.round112AgdaPhysicalThreeSlotInternalPaymentPortClosed

round113UniformGalerkinCriticalBarrierClosed : Bool
round113UniformGalerkinCriticalBarrierClosed =
  R112.round112UniformGalerkinCriticalBarrierClosed

round113PhysicalCriticalSobolevSimonUpgradeClosed : Bool
round113PhysicalCriticalSobolevSimonUpgradeClosed =
  R112.round112PhysicalCriticalSobolevSimonUpgradeClosed

round113CurrentMathematicalPackageCount : Nat
round113CurrentMathematicalPackageCount = 2

round113CurrentVisibleSubleafCount : Nat
round113CurrentVisibleSubleafCount = 3

round113CurrentAgdaPortGapCount : Nat
round113CurrentAgdaPortGapCount = 1

round113WeightedAntisymmetricPairMultiplierDifferenceClosedIsTrue :
  round113WeightedAntisymmetricPairMultiplierDifferenceClosed ≡ true
round113WeightedAntisymmetricPairMultiplierDifferenceClosedIsTrue = refl

round113RealitySymmetryAloneGivesMultiplierDifferenceIsFalse :
  round113RealitySymmetryAloneGivesMultiplierDifference ≡ false
round113RealitySymmetryAloneGivesMultiplierDifferenceIsFalse = refl

round113PhysicalExternalCrossTriadAntisymmetricReindexWeldClosedIsFalse :
  round113PhysicalExternalCrossTriadAntisymmetricReindexWeldClosed ≡ false
round113PhysicalExternalCrossTriadAntisymmetricReindexWeldClosedIsFalse = refl

round113PhysicalExternalResidualCutoffUniformQuantitativePaymentClosedIsFalse :
  round113PhysicalExternalResidualCutoffUniformQuantitativePaymentClosed ≡ false
round113PhysicalExternalResidualCutoffUniformQuantitativePaymentClosedIsFalse = refl

round113PhysicalExternalCrossTriadIntegratedResiduePaymentClosedIsFalse :
  round113PhysicalExternalCrossTriadIntegratedResiduePaymentClosed ≡ false
round113PhysicalExternalCrossTriadIntegratedResiduePaymentClosedIsFalse = refl

round113AgdaPhysicalThreeSlotInternalPaymentPortClosedIsFalse :
  round113AgdaPhysicalThreeSlotInternalPaymentPortClosed ≡ false
round113AgdaPhysicalThreeSlotInternalPaymentPortClosedIsFalse = refl

round113UniformGalerkinCriticalBarrierClosedIsFalse :
  round113UniformGalerkinCriticalBarrierClosed ≡ false
round113UniformGalerkinCriticalBarrierClosedIsFalse = refl

round113PhysicalCriticalSobolevSimonUpgradeClosedIsFalse :
  round113PhysicalCriticalSobolevSimonUpgradeClosed ≡ false
round113PhysicalCriticalSobolevSimonUpgradeClosedIsFalse = refl

round113CurrentMathematicalPackageCountIsTwo :
  round113CurrentMathematicalPackageCount ≡ 2
round113CurrentMathematicalPackageCountIsTwo = refl

round113CurrentVisibleSubleafCountIsThree :
  round113CurrentVisibleSubleafCount ≡ 3
round113CurrentVisibleSubleafCountIsThree = refl

round113CurrentAgdaPortGapCountIsOne :
  round113CurrentAgdaPortGapCount ≡ 1
round113CurrentAgdaPortGapCountIsOne = refl

round113ClayPromotion : Bool
round113ClayPromotion = false

round113ClayPromotionIsFalse : round113ClayPromotion ≡ false
round113ClayPromotionIsFalse = refl
