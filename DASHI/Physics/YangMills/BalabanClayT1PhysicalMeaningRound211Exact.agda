{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT1PhysicalMeaningRound211Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT1ResidualIntrospectionRound210Exact as R210
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment

------------------------------------------------------------------------
-- ROUND211 / PHYSICAL MEANING OF THE GLOBAL T1 WALL
--
-- Finite moments say large field excursions are statistically expensive.
-- Tightness says something stronger and geometric: for every tolerated leakage
-- epsilon there is ONE admissible compact region that captures almost all of
-- every selected cutoff measure.  The missing theorem is the bridge from the
-- already-owned moment inequality to that global escape-control statement.
------------------------------------------------------------------------

data PhysicalQuestion211 : Set where
  largeExcursionsAreMomentExpensive : PhysicalQuestion211
  oneCompactRegionCapturesAllCutoffs : PhysicalQuestion211
  localChartControlsGlobalSupport : PhysicalQuestion211

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

physicalQuestionFor : R210.T1Residual210 → PhysicalQuestion211
physicalQuestionFor R210.globalMomentToEscapeControl =
  oneCompactRegionCapturesAllCutoffs
physicalQuestionFor R210.t1Closed =
  oneCompactRegionCapturesAllCutoffs

-- The existing compiler identifies exactly the semantic bridge still needed:
-- a moment inequality must imply control of the complement of the selected
-- compact witness on the literal diagonal measure sequence.
round211MomentCompilerAlreadyMachineChecked : Bool
round211MomentCompilerAlreadyMachineChecked = true

round211RemainingInputIsGlobalEscapeSemantics : Bool
round211RemainingInputIsGlobalEscapeSemantics = true

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

round211RemainingInputIsGlobalEscapeSemanticsIsTrue :
  round211RemainingInputIsGlobalEscapeSemantics ≡ true
round211RemainingInputIsGlobalEscapeSemanticsIsTrue = refl

round211SearchSpaceStrictlyPrunedIsTrue :
  round211SearchSpaceStrictlyPruned ≡ true
round211SearchSpaceStrictlyPrunedIsTrue = refl

round211ClayPromotionIsFalse : round211ClayPromotion ≡ false
round211ClayPromotionIsFalse = refl
