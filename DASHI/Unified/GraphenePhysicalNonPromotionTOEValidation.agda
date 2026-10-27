module DASHI.Unified.GraphenePhysicalNonPromotionTOEValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.GraphenePhysicalNonPromotionTOEExact as Bridge

grapheneAndIronRemainDifferentPhysicalObjects :
  Bridge.grapheneIsSamePhysicalObjectAsIron ≡ false
grapheneAndIronRemainDifferentPhysicalObjects = refl

observedQTMIntensityIsNotProvedBySyntheticObserver :
  Bridge.syntheticQTMCountsAsMeasuredFit ≡ false
observedQTMIntensityIsNotProvedBySyntheticObserver = refl

measuredEntropyIsNotProvedBySyntheticMaxwell :
  Bridge.syntheticMaxwellCountsAsMeasuredEntropy ≡ false
measuredEntropyIsNotProvedBySyntheticMaxwell = refl

warpGeometryIsNotProvedByPositiveEulerianEnergy :
  Bridge.positiveEulerianCountsAsFullWEC ≡ false
warpGeometryIsNotProvedByPositiveEulerianEnergy = refl

grapheneSourceAttributionIsRetained :
  Bridge.grapheneSourceAttributionRetained ≡ true
grapheneSourceAttributionIsRetained = refl
