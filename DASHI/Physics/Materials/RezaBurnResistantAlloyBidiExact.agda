module DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Patent family US20030053926A1 / US20040208777A1.
-- Composition intervals are source-owned design coordinates, not universal laws.

data AlloyElement : Set where nickel cobalt chromium aluminum titanium : AlloyElement

record WeightPercentRange : Set where
  constructor wt-range
  field
    element : AlloyElement
    minimum maximum : ℕ
    sourceReference : String

open WeightPercentRange public

nickelRange : WeightPercentRange
nickelRange = wt-range nickel 55 75 "Jacinto/Hardwick patent: about 55-75 wt% Ni"

cobaltRange : WeightPercentRange
cobaltRange = wt-range cobalt 12 17 "Jacinto/Hardwick patent: about 12-17 wt% Co"

chromiumRange : WeightPercentRange
chromiumRange = wt-range chromium 4 16 "Jacinto/Hardwick patent: about 4-16 wt% Cr"

aluminumRange : WeightPercentRange
aluminumRange = wt-range aluminum 1 4 "Jacinto/Hardwick patent: about 1-4 wt% Al"

titaniumRange : WeightPercentRange
titaniumRange = wt-range titanium 1 4 "Jacinto/Hardwick patent: about 1-4 wt% Ti"

record AlloyRole : Set where
  constructor alloy-role
  field
    roleElement : AlloyElement
    claimedRole : String
    roleReference : String

open AlloyRole public

nickelBurnResistance : AlloyRole
nickelBurnResistance = alloy-role nickel "principal burn-resistance carrier at high Ni fraction" "US20030053926A1 description"

cobaltSolidSolutionStrength : AlloyRole
cobaltSolidSolutionStrength = alloy-role cobalt "solid-solution strengthening while retaining burn resistance" "US20030053926A1 description"

chromiumOxidationResistance : AlloyRole
chromiumOxidationResistance = alloy-role chromium "oxidation resistance contribution" "US20030053926A1 description"

aluminumOxidationResistance : AlloyRole
aluminumOxidationResistance = alloy-role aluminum "oxidation resistance while maintaining burn resistance" "US20030053926A1 description"

record RezaAlloyBoundary : Set where
  constructor reza-alloy-boundary
  field
    compositionRangeGuaranteesPerformanceWithoutProcessingState : Bool
    compositionRangeGuaranteesPerformanceWithoutProcessingStateIsFalse : compositionRangeGuaranteesPerformanceWithoutProcessingState ≡ false
    oneElementAloneExplainsFullStrengthBurnTradeoff : Bool
    oneElementAloneExplainsFullStrengthBurnTradeoffIsFalse : oneElementAloneExplainsFullStrengthBurnTradeoff ≡ false
    patentCompositionIsUniversalNickelSuperalloyLaw : Bool
    patentCompositionIsUniversalNickelSuperalloyLawIsFalse : patentCompositionIsUniversalNickelSuperalloyLaw ≡ false

canonicalRezaAlloyBoundary : RezaAlloyBoundary
canonicalRezaAlloyBoundary = reza-alloy-boundary false refl false refl false refl
