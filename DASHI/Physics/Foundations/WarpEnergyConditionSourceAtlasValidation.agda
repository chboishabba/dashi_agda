module DASHI.Physics.Foundations.WarpEnergyConditionSourceAtlasValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.WarpEnergyConditionSourceAtlasExact as W

generic-standard-gr-violation-source-paid : W.genericPhysicallyReasonableWarpEnergyConditionViolationSourcePaid W.canonicalWarpEnergyConditionSourceAtlas ≡ true
generic-standard-gr-violation-source-paid = refl

subluminal-positive-energy-construction-source-paid : W.constantVelocitySubluminalPositiveEnergyConstructionSourcePaid W.canonicalWarpEnergyConditionSourceAtlas ≡ true
subluminal-positive-energy-construction-source-paid = refl

subluminal-does-not-promote-ftl : W.subluminalPositiveEnergyConstructionCountsAsFTL W.canonicalWarpEnergyConditionSourceAtlas ≡ false
subluminal-does-not-promote-ftl = refl

source-theorem-does-not-create-physical-device : W.sourceTheoremCountsAsPhysicalWarpDevice W.canonicalWarpEnergyConditionSourceAtlas ≡ false
source-theorem-does-not-create-physical-device = refl

positive-energy-one-construction-does-not-refute-generic-theorem : W.positiveEnergySubluminalConstructionRefutesGenericStandardGRResult W.canonicalWarpEnergyConditionSourceAtlas ≡ false
positive-energy-one-construction-does-not-refute-generic-theorem = refl

superluminal-positive-energy-remains-unpaid : W.superluminalPositiveEnergyPhysicalSourcePaid W.canonicalWarpEnergyConditionSourceAtlas ≡ false
superluminal-positive-energy-remains-unpaid = refl
