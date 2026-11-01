module DASHI.Biology.Agriculture.BNFEconomicValidationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Agriculture.HungriaEconomicEmissionModel2023Exact as Model2023
import DASHI.Biology.Agriculture.Hungria2024HeadlineLineageWeldExact as Headline2024
import DASHI.Biology.Agriculture.HungriaSourceAttributionPromotionBoundaryExact as Attribution

------------------------------------------------------------------------
-- BNF ECONOMIC-VALIDATION CROSS-POLLINATION
--
-- Retrospective theorem-pattern cross-pollination from the AI infrastructure
-- economics tranche.  We intentionally do NOT import the draft economics PR:
-- this agriculture owner carries the reusable distinctions without creating
-- draft-PR ancestry.
--
-- The shared pattern is structural, not historical or semantic identity:
--
--   observed technical success != complete economic validation
--   gross/reported savings       != net realized beneficiary value
--   multiple adopters/projects   != independent ultimate economic drivers
--   scarcity/input-price shock   != downstream viability
--   policy support               != positive commercial value
--   finite historical fit        != universal future law
--   multi-axis regime vector     != one-bit "bubble"/"miracle" label.
--
-- None of these theorem shapes is attributed to Hungria, Telles, Nogueira,
-- Embrapa, or the World Food Prize Foundation.
------------------------------------------------------------------------

data EconomicCoordinate : Set where
  avoidedFertilizerExpenditure : EconomicCoordinate
  inoculantCost : EconomicCoordinate
  applicationCost : EconomicCoordinate
  yieldEffect : EconomicCoordinate
  yieldRisk : EconomicCoordinate
  financingCost : EconomicCoordinate
  realizedFarmerCashBenefit : EconomicCoordinate
  publicSupport : EconomicCoordinate
  ureaPriceExposure : EconomicCoordinate
  inoculantSupplyExposure : EconomicCoordinate
  emissionAccountingBenefit : EconomicCoordinate


data ObservationStatus : Set where
  sourceObserved : ObservationStatus
  modelComputed : ObservationStatus
  beneficiaryRealizationOpen : ObservationStatus
  futureRegimeOpen : ObservationStatus

record BNFEconomicValidationVector : Set where
  constructor bnfEconomicValidationVector
  field
    avoidedFertilizerSpend : ObservationStatus
    inoculantUnitCost : ObservationStatus
    applicationCostStatus : ObservationStatus
    yieldEffectStatus : ObservationStatus
    realizedFarmerCashStatus : ObservationStatus
    ureaPriceSensitivity : ObservationStatus
    inoculantSupplySensitivity : ObservationStatus
    policySupportStatus : ObservationStatus
    emissionBenefitStatus : ObservationStatus

open BNFEconomicValidationVector public

current2019_2020ValidationVector : BNFEconomicValidationVector
current2019_2020ValidationVector =
  bnfEconomicValidationVector
    modelComputed
    sourceObserved
    beneficiaryRealizationOpen
    sourceObserved
    beneficiaryRealizationOpen
    sourceObserved
    futureRegimeOpen
    futureRegimeOpen
    modelComputed

------------------------------------------------------------------------
-- Unit-economics analogue.
--
-- The Telles 2023 avoided-urea value is a counterfactual gross saving.  A
-- beneficiary-level net-value receipt must still account for inoculant,
-- application, yield, risk and financing coordinates on the same farm/time.
------------------------------------------------------------------------

record FarmUnitEconomicsReceipt : Set₁ where
  constructor farmUnitEconomicsReceipt
  field
    Farm Season : Set
    farm : Farm
    season : Season
    avoidedFertilizerCost : Set
    inoculantCostPaid : Set
    applicationCostPaid : Set
    yieldOutcome : Set
    otherIncrementalCosts : Set
    realizedNetCashBenefit : Set
    sameFarmSameSeasonWeld : Set

open FarmUnitEconomicsReceipt public

data GrossAvoidedCostImpliesNetFarmerBenefitPermission : Set where

data HighAdoptionImpliesPositiveFarmUnitEconomicsPermission : Set where

data PositiveModelledBenefitImpliesEveryFarmBenefitsPermission : Set where

grossAvoidedCostDoesNotAutoPromoteToNetFarmerBenefit :
  GrossAvoidedCostImpliesNetFarmerBenefitPermission → ⊥
grossAvoidedCostDoesNotAutoPromoteToNetFarmerBenefit ()

highAdoptionDoesNotAutoPromoteToPositiveFarmUnitEconomics :
  HighAdoptionImpliesPositiveFarmUnitEconomicsPermission → ⊥
highAdoptionDoesNotAutoPromoteToPositiveFarmUnitEconomics ()

positiveModelledBenefitDoesNotAutoPromoteToEveryFarm :
  PositiveModelledBenefitImpliesEveryFarmBenefitsPermission → ⊥
positiveModelledBenefitDoesNotAutoPromoteToEveryFarm ()

------------------------------------------------------------------------
-- Terminal-beneficiary analogue.
--
-- In AI work, terminal-payer validation asks whether external cash generation
-- ultimately pays depreciation/debt/return/replacement capex.  For BNF, the
-- corresponding economic consumer is the farmer/farm system that actually
-- retains net value after the relevant substitution and implementation costs.
------------------------------------------------------------------------

record TerminalFarmerBenefitReceipt : Set₁ where
  constructor terminalFarmerBenefitReceipt
  field
    Farmer Farm Season : Set
    farmer : Farmer
    farm : Farm
    season : Season
    avoidedCashOutflow : Set
    inoculantCashOutflow : Set
    applicationCashOutflow : Set
    yieldOrRevenueEffect : Set
    financingAndTransitionCosts : Set
    positiveNetFarmerBenefit : Set
    independentOfPureAccountingReclassification : Set

open TerminalFarmerBenefitReceipt public

data NationalAvoidedCostImpliesTerminalFarmerBenefitPermission : Set where

data InstitutionalSavingsHeadlineImpliesCashRealizationPermission : Set where

nationalAvoidedCostDoesNotAutoPromoteToTerminalFarmerBenefit :
  NationalAvoidedCostImpliesTerminalFarmerBenefitPermission → ⊥
nationalAvoidedCostDoesNotAutoPromoteToTerminalFarmerBenefit ()

institutionalHeadlineDoesNotAutoPromoteToCashRealization :
  InstitutionalSavingsHeadlineImpliesCashRealizationPermission → ⊥
institutionalHeadlineDoesNotAutoPromoteToCashRealization ()

------------------------------------------------------------------------
-- Common-factor / provenance analogue.
--
-- Many farms, states or seasons can still depend on a shared ultimate driver:
-- urea price, soybean price, weather, inoculant supply, credit conditions, or
-- one accounting assumption.  Multiplicity does not manufacture independence.
------------------------------------------------------------------------

data UltimateEconomicDriver : Set where
  ureaPriceDriver : UltimateEconomicDriver
  soybeanPriceDriver : UltimateEconomicDriver
  weatherDriver : UltimateEconomicDriver
  inoculantSupplyDriver : UltimateEconomicDriver
  financingDriver : UltimateEconomicDriver
  accountingAssumptionDriver : UltimateEconomicDriver

record AgriculturalEconomicExposure : Set₁ where
  constructor agriculturalEconomicExposure
  field
    Unit : Set
    ultimateDriver : Unit → UltimateEconomicDriver

open AgriculturalEconomicExposure public

data FarmMultiplicityImpliesDriverIndependencePermission : Set where

data StateMultiplicityImpliesDriverIndependencePermission : Set where

farmMultiplicityDoesNotAutoPromoteToDriverIndependence :
  FarmMultiplicityImpliesDriverIndependencePermission → ⊥
farmMultiplicityDoesNotAutoPromoteToDriverIndependence ()

stateMultiplicityDoesNotAutoPromoteToDriverIndependence :
  StateMultiplicityImpliesDriverIndependencePermission → ⊥
stateMultiplicityDoesNotAutoPromoteToDriverIndependence ()

------------------------------------------------------------------------
-- Scarcity / price-regime analogue.
------------------------------------------------------------------------

record AgriculturalInputScarcityRegime : Set₁ where
  constructor agriculturalInputScarcityRegime
  field
    Time : Set
    UreaCapacity UreaDemand UreaPrice InoculantCapacity InoculantDemand : Time → Set
    scarcityObserved : Time → Set

open AgriculturalInputScarcityRegime public

data HighUreaPriceImpliesBNFAlwaysEconomicallySuperiorPermission : Set where

data InoculantScarcityImpliesTechnologyFailurePermission : Set where

highUreaPriceDoesNotAutoPromoteToUniversalBNFSuperiority :
  HighUreaPriceImpliesBNFAlwaysEconomicallySuperiorPermission → ⊥
highUreaPriceDoesNotAutoPromoteToUniversalBNFSuperiority ()

inoculantScarcityDoesNotAutoPromoteToTechnologyFailure :
  InoculantScarcityImpliesTechnologyFailurePermission → ⊥
inoculantScarcityDoesNotAutoPromoteToTechnologyFailure ()

------------------------------------------------------------------------
-- Policy-support analogue.
------------------------------------------------------------------------

data PolicySupportImpliesPrivateNetBenefitPermission : Set where

data StrategicAgronomicValueImpliesPositiveFarmNPVPermission : Set where

policySupportDoesNotAutoPromoteToPrivateNetBenefit :
  PolicySupportImpliesPrivateNetBenefitPermission → ⊥
policySupportDoesNotAutoPromoteToPrivateNetBenefit ()

strategicValueDoesNotAutoPromoteToPositiveFarmNPV :
  StrategicAgronomicValueImpliesPositiveFarmNPVPermission → ⊥
strategicValueDoesNotAutoPromoteToPositiveFarmNPV ()

------------------------------------------------------------------------
-- Multi-axis regime classifier: deliberately not MiracleTechnology : Bool.
------------------------------------------------------------------------

record BNFAgronomicEconomicRegimeVector : Set₁ where
  constructor bnfAgronomicEconomicRegimeVector
  field
    BiologicalEfficacy MineralNSubstitution UnitEconomics AdoptionScale
      UreaPriceSensitivity InoculantSupplyRisk PolicySupport
      EmissionAccountingConfidence : Set
    biologicalEfficacy : BiologicalEfficacy
    mineralNSubstitution : MineralNSubstitution
    unitEconomics : UnitEconomics
    adoptionScale : AdoptionScale
    ureaPriceSensitivity : UreaPriceSensitivity
    inoculantSupplyRisk : InoculantSupplyRisk
    policySupport : PolicySupport
    emissionAccountingConfidence : EmissionAccountingConfidence

open BNFAgronomicEconomicRegimeVector public

data RegimeVectorImpliesMiracleTechnologyPermission : Set where

data HistoricalEconomicFitImpliesUniversalFutureSavingsLawPermission : Set where

regimeVectorDoesNotAutoPromoteToMiracleTechnology :
  RegimeVectorImpliesMiracleTechnologyPermission → ⊥
regimeVectorDoesNotAutoPromoteToMiracleTechnology ()

historicalFitDoesNotAutoPromoteToUniversalFutureSavingsLaw :
  HistoricalEconomicFitImpliesUniversalFutureSavingsLawPermission → ⊥
historicalFitDoesNotAutoPromoteToUniversalFutureSavingsLaw ()

------------------------------------------------------------------------
-- Current source-version facts retained from the BNF lane.
------------------------------------------------------------------------

paper2019_2020AvoidedCost = Model2023.avoidedUreaCostIs15200MillionUSD
paper2019_2020Mitigation = Model2023.mitigationIs183MillionMg
headline2024ReplayStillOpen = Headline2024.calculationReplayStillOpen
quoteDoesNotSupplyReplay = Attribution.speakerQuoteDoesNotSupplyCalculationReplay
