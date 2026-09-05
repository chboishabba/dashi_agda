module DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Patent family US20030053926A1 / US20040208777A1.
-- Composition intervals, strengthening mechanisms, processing and tested
-- examples are source-owned design coordinates, not universal alloy laws.

data AlloyElement : Set where nickel cobalt chromium aluminum titanium carbon boron zirconium manganese : AlloyElement

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
nickelBurnResistance = alloy-role nickel "principal burn-resistance carrier at high Ni fraction" "US20030053926A1 para 0020"

cobaltSolidSolutionStrength : AlloyRole
cobaltSolidSolutionStrength = alloy-role cobalt "solid-solution strengthening in nickel matrix while maintaining burn resistance" "US20030053926A1 para 0021"

chromiumOxidationResistance : AlloyRole
chromiumOxidationResistance = alloy-role chromium "minimum oxidation-resistance contribution" "US20030053926A1 para 0022"

aluminumGammaPrimeAndOxidation : AlloyRole
aluminumGammaPrimeAndOxidation = alloy-role aluminum "oxidation resistance plus gamma-prime strengthening contribution" "US20030053926A1 para 0023"

titaniumGammaPrime : AlloyRole
titaniumGammaPrime = alloy-role titanium "gamma-prime strengthening contribution" "US20030053926A1 para 0024"

boronGrainBoundaryStrength : AlloyRole
boronGrainBoundaryStrength = alloy-role boron "minor-element grain-boundary strengthening during fabrication" "US20030053926A1 para 0025"

zirconiumGrainBoundaryStrength : AlloyRole
zirconiumGrainBoundaryStrength = alloy-role zirconium "minor-element grain-boundary strengthening during fabrication" "US20030053926A1 para 0025"

carbonGrainBoundaryStrength : AlloyRole
carbonGrainBoundaryStrength = alloy-role carbon "minor-element grain-boundary strengthening during fabrication" "US20030053926A1 para 0025"


data ProcessStage : Set where
  vacuumInductionMelting vacuumArcRemelting mechanicalWorking finalProductForm : ProcessStage

record ProcessChain : Set where
  constructor process-chain
  field
    stages : List ProcessStage
    processReference : String

open ProcessChain public

canonicalPatentProcess : ProcessChain
canonicalPatentProcess = process-chain
  (vacuumInductionMelting ∷ vacuumArcRemelting ∷ mechanicalWorking ∷ finalProductForm ∷ [])
  "Patent para 0026: two-step melting followed by mechanical working into billet/bar/sheet/plate"

record TestedAlloyExample : Set where
  constructor tested-alloy-example
  field
    label : String
    nickelWt cobaltWt chromiumWt : String
    aluminumWt titaniumWt : String
    tensileStrengthKsi : String
    extinguishingThresholdPsi : String
    testEnvironment : String
    sourceReference : String

open TestedAlloyExample public

example1 : TestedAlloyExample
example1 = tested-alloy-example
  "Example 1"
  "71.5" "16.5" "8.0" "1.5" "2.5"
  "~170 from patent figure / described as high enough for most cited rocket-engine environments"
  "at least about 10000 in continuation text"
  "high-pressure gaseous oxygen, harsher than or similar to oxygen-rich/full-flow staged combustion"
  "US20030053926A1 / US20040208777A1 examples and Figure 1"

example2 : TestedAlloyExample
example2 = tested-alloy-example
  "Example 2"
  "69.9" "16.6" "8.1" "1.5" "3.9"
  "about 187"
  "about 7000"
  "high-pressure gaseous oxygen, harsher than or similar to oxygen-rich/full-flow staged combustion"
  "US20040208777A1 para 0028"

record StrengthBurnTradeoff : Set where
  constructor strength-burn-tradeoff
  field
    gammaPrimeStrengtheningCanIncreaseStrength : Bool
    gammaPrimeStrengtheningCanIncreaseStrengthIsTrue :
      gammaPrimeStrengtheningCanIncreaseStrength ≡ true
    gammaPrimeFormationCanDecreaseBurnResistance : Bool
    gammaPrimeFormationCanDecreaseBurnResistanceIsTrue :
      gammaPrimeFormationCanDecreaseBurnResistance ≡ true
    tradeoffReference : String

open StrengthBurnTradeoff public

canonicalStrengthBurnTradeoff : StrengthBurnTradeoff
canonicalStrengthBurnTradeoff = strength-burn-tradeoff
  true refl
  true refl
  "US20040208777A1 para 0029: Al/Ti gamma-prime formers increase selected strength while gamma-prime formations can decrease burn resistance"

record RezaAlloyBoundary : Set where
  constructor reza-alloy-boundary
  field
    compositionRangeGuaranteesPerformanceWithoutProcessingState : Bool
    compositionRangeGuaranteesPerformanceWithoutProcessingStateIsFalse : compositionRangeGuaranteesPerformanceWithoutProcessingState ≡ false
    oneElementAloneExplainsFullStrengthBurnTradeoff : Bool
    oneElementAloneExplainsFullStrengthBurnTradeoffIsFalse : oneElementAloneExplainsFullStrengthBurnTradeoff ≡ false
    patentCompositionIsUniversalNickelSuperalloyLaw : Bool
    patentCompositionIsUniversalNickelSuperalloyLawIsFalse : patentCompositionIsUniversalNickelSuperalloyLaw ≡ false
    moreGammaPrimeAlwaysImprovesOverallDesign : Bool
    moreGammaPrimeAlwaysImprovesOverallDesignIsFalse : moreGammaPrimeAlwaysImprovesOverallDesign ≡ false
    testedExampleAutomaticallyGeneralisesToWholeCompositionBox : Bool
    testedExampleAutomaticallyGeneralisesToWholeCompositionBoxIsFalse : testedExampleAutomaticallyGeneralisesToWholeCompositionBox ≡ false
    extinguishingThresholdAndTensileStrengthAreDistinctObjectives : Bool
    extinguishingThresholdAndTensileStrengthAreDistinctObjectivesIsTrue : extinguishingThresholdAndTensileStrengthAreDistinctObjectives ≡ true

canonicalRezaAlloyBoundary : RezaAlloyBoundary
canonicalRezaAlloyBoundary = reza-alloy-boundary
  false refl false refl false refl false refl false refl true refl

record AlloyDesignReverseObligation : Set where
  constructor alloy-design-reverse-obligation
  field
    candidateComposition : String
    processingReceipt : String
    microstructureReceipt : String
    tensileTestReceipt : String
    burnThresholdReceipt : String
    oxidationReceipt : String
    promotes : String
    cannotPromote : String

open AlloyDesignReverseObligation public

rocketEngineAlloyReverse : AlloyDesignReverseObligation
rocketEngineAlloyReverse = alloy-design-reverse-obligation
  "candidate Ni-Co-Cr-Al-Ti composition inside patent ranges"
  "melting/remelting/mechanical-work and heat-treatment history"
  "gamma-prime fraction/morphology and grain-boundary state"
  "temperature-specific tensile-strength test"
  "high-pressure oxygen extinguishing-combustion-threshold test"
  "oxidation-resistance test under relevant temperature/environment"
  "source-bounded strength/burn-resistance design claim"
  "universal rocket-engine suitability from nominal composition alone"
