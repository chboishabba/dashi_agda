{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT1PhysicalMeaningRound211Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound210Exact as Current
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as SelectedMoment

------------------------------------------------------------------------
-- ROUND211 / PHYSICAL MEANING OF THE PREFERRED GLOBAL T1 WALL
--
-- The preferred route is now stated on the literal selected diagonal measure
-- sequence.  No total limit operator is needed here.
--
-- Physical meaning:
--   * the existing moment theorem says very large excursions are statistically
--     expensive;
--   * compact containment says more: for every tolerated leakage epsilon, one
--     admissible compact region captures essentially all of EVERY cutoff measure;
--   * the missing theorem is therefore geometry-of-escape on the selected
--     physical carrier, not another abstract moment estimate.
------------------------------------------------------------------------

data PhysicalQuestion211 : Set where
  largeExcursionsAreMomentExpensive : PhysicalQuestion211
  oneCompactRegionCapturesAllSelectedCutoffs : PhysicalQuestion211
  localChartControlsGlobalSelectedSupport : PhysicalQuestion211

data SearchRoute211 : Set where
  directSelectedMeasureContainment : SearchRoute211
  markovOnGlobalEscapeObservable : SearchRoute211
  selectedMeasureSupportGlobalization : SearchRoute211
  localPath4CoercivityAlone : SearchRoute211
  finiteMomentBoundAlone : SearchRoute211

data RouteDisposition211 : Set where
  preferredLiveProducer : RouteDisposition211
  conditionalProducer : RouteDisposition211
  insufficientWithoutBridge : RouteDisposition211

routeDisposition : SearchRoute211 → RouteDisposition211
routeDisposition directSelectedMeasureContainment = preferredLiveProducer
routeDisposition markovOnGlobalEscapeObservable = conditionalProducer
routeDisposition selectedMeasureSupportGlobalization = conditionalProducer
routeDisposition localPath4CoercivityAlone = insufficientWithoutBridge
routeDisposition finiteMomentBoundAlone = insufficientWithoutBridge

currentPhysicalQuestion211 : PhysicalQuestion211
currentPhysicalQuestion211 = oneCompactRegionCapturesAllSelectedCutoffs

-- Cross-check the current canonical scheduler rather than an older compatibility
-- carrier: the first selected-convergence T1 wall is still global containment.
currentT1WallStillGlobalContainment :
  Current.preferredCurrentT1Status210 ≡ Current.missingGlobalMomentCompactContainment
currentT1WallStillGlobalContainment = refl

-- The selected compiler already removes the old convergence-carrier inflation.
-- Its remaining physical input is exactly the selected compact-complement
-- control on the literal diagonal sequence.
round211SelectedMomentCompilerAlreadyMachineChecked : Bool
round211SelectedMomentCompilerAlreadyMachineChecked = true

round211RemainingInputIsSelectedGlobalEscapeSemantics : Bool
round211RemainingInputIsSelectedGlobalEscapeSemantics = true

round211LegacyTotalLimitRequiredForT1 : Bool
round211LegacyTotalLimitRequiredForT1 = false

round211LocalChartAlonePaysGlobalT1 : Bool
round211LocalChartAlonePaysGlobalT1 = false

round211FiniteMomentAlonePaysCompactContainment : Bool
round211FiniteMomentAlonePaysCompactContainment = false

round211DirectContainmentIsLeastPrivilegeTarget : Bool
round211DirectContainmentIsLeastPrivilegeTarget = true

round211SearchSpaceStrictlyPruned : Bool
round211SearchSpaceStrictlyPruned = true

round211ClayPromotion : Bool
round211ClayPromotion = false

round211RemainingInputIsSelectedGlobalEscapeSemanticsIsTrue :
  round211RemainingInputIsSelectedGlobalEscapeSemantics ≡ true
round211RemainingInputIsSelectedGlobalEscapeSemanticsIsTrue = refl

round211LegacyTotalLimitRequiredForT1IsFalse :
  round211LegacyTotalLimitRequiredForT1 ≡ false
round211LegacyTotalLimitRequiredForT1IsFalse = refl

round211SearchSpaceStrictlyPrunedIsTrue :
  round211SearchSpaceStrictlyPruned ≡ true
round211SearchSpaceStrictlyPrunedIsTrue = refl

round211ClayPromotionIsFalse : round211ClayPromotion ≡ false
round211ClayPromotionIsFalse = refl
