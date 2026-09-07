module DASHI.Biology.Agriculture.Hungria2024EconomicReplayInputAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Agriculture.HungriaEconomicEmissionModel2023Exact as Model2023
import DASHI.Biology.Agriculture.Hungria2024HeadlineLineageWeldExact as Headline
import DASHI.Biology.Agriculture.BNFEconomicValidationCrossPollinationExact as EconX

------------------------------------------------------------------------
-- 2024 REPLAY INPUT AUDIT
--
-- Public-source receipts recovered so far:
--
--   CONAB 12th and final 2023/24 grain survey (12 Sep 2024):
--     Brazilian soybean production = 147.38 million tonnes.
--
--   CONAB agricultural-input price system exposes state/month 2024 urea-price
--   observations.  Example: Minas Gerais has explicit monthly URÉIA and
--   URÉIA 45 records.  This establishes that a 2024 price producer exists, but
--   one state's displayed price series is not a Brazil-wide weighted urea-N
--   price and is not silently substituted for the Telles model input.
--
--   Embrapa 2025 reports about USD 25B savings and >230 Mt CO2-e for 2024.
--
-- We therefore distinguish "input producer located" from "same-object value
-- extracted and replayed".  The latter remains open.
------------------------------------------------------------------------

data ReplayCoordinate : Set where
  soybeanProduction2023_24 : ReplayCoordinate
  soybeanArea2023_24 : ReplayCoordinate
  stateYieldVector2023_24 : ReplayCoordinate
  stateAreaVector2023_24 : ReplayCoordinate
  stateUreaPriceVector2024 : ReplayCoordinate
  brazilWeightedUreaNPrice2024 : ReplayCoordinate
  secondaryNAssumption2024 : ReplayCoordinate
  fertilizerRecoveryAssumption2024 : ReplayCoordinate
  emissionCoefficient2024 : ReplayCoordinate
  exactModelEquationIdentity : ReplayCoordinate
  exactOutputReplay : ReplayCoordinate


data ProducerStatus : Set where
  authoritativeValueRecovered : ProducerStatus
  authoritativeProducerLocated : ProducerStatus
  assumptionLineageKnownFrom2023 : ProducerStatus
  openProducer : ProducerStatus

replayStatus : ReplayCoordinate → ProducerStatus
replayStatus soybeanProduction2023_24 = authoritativeValueRecovered
replayStatus soybeanArea2023_24 = authoritativeProducerLocated
replayStatus stateYieldVector2023_24 = authoritativeProducerLocated
replayStatus stateAreaVector2023_24 = authoritativeProducerLocated
replayStatus stateUreaPriceVector2024 = authoritativeProducerLocated
replayStatus brazilWeightedUreaNPrice2024 = openProducer
replayStatus secondaryNAssumption2024 = assumptionLineageKnownFrom2023
replayStatus fertilizerRecoveryAssumption2024 = assumptionLineageKnownFrom2023
replayStatus emissionCoefficient2024 = assumptionLineageKnownFrom2023
replayStatus exactModelEquationIdentity = openProducer
replayStatus exactOutputReplay = openProducer

soybeanProductionValueRecovered :
  replayStatus soybeanProduction2023_24 ≡ authoritativeValueRecovered
soybeanProductionValueRecovered = refl

ureaPriceProducerLocated :
  replayStatus stateUreaPriceVector2024 ≡ authoritativeProducerLocated
ureaPriceProducerLocated = refl

weightedBrazilUreaPriceStillOpen :
  replayStatus brazilWeightedUreaNPrice2024 ≡ openProducer
weightedBrazilUreaPriceStillOpen = refl

exactReplayStillOpen : replayStatus exactOutputReplay ≡ openProducer
exactReplayStillOpen = refl

------------------------------------------------------------------------
-- Exact source-valued aggregate retained as an integer in thousand tonnes.
-- 147.38 million tonnes = 147,380 thousand tonnes.
------------------------------------------------------------------------

conabSoybeanProductionThousandTonnes2023_24 : Nat
conabSoybeanProductionThousandTonnes2023_24 = 147380

conabProductionIs147380ThousandTonnes :
  conabSoybeanProductionThousandTonnes2023_24 ≡ 147380
conabProductionIs147380ThousandTonnes = refl

record InputReceipt : Set where
  constructor inputReceipt
  field
    coordinate : ReplayCoordinate
    producer : String
    sourceLocation : String
    valueOrStatus : String
    admissibleUse : String
    excludedPromotion : String

open InputReceipt public

conabProductionReceipt : InputReceipt
conabProductionReceipt =
  inputReceipt
    soybeanProduction2023_24
    "Companhia Nacional de Abastecimento (CONAB)"
    "12th/final Survey of the 2023/24 Grain Harvest, 12 September 2024"
    "Soybean production 147.38 million tonnes"
    "Authoritative national production aggregate for the 2023/24 crop"
    "Does not reconstruct state-level area/yield vectors, fertilizer counterfactual, urea price or the USD 25B headline"

conabUreaPriceSystemReceipt : InputReceipt
conabUreaPriceSystemReceipt =
  inputReceipt
    stateUreaPriceVector2024
    "CONAB agricultural-input price consultation system"
    "Insumos Agropecuários, fertilizer/chemical, state and month indexed"
    "2024 state/month urea price records are publicly exposed; Minas Gerais is one verified example"
    "Producer surface for state/month fertilizer prices"
    "One state/month observation does not become the Brazil-wide weighted urea-N price used by a national replay"

------------------------------------------------------------------------
-- Cross-pollination with the AI/economic-regime lesson:
-- a historical fitted/modelled relationship is not a universal future law.
------------------------------------------------------------------------

data PaperModelImpliesSame2024ParametersPermission : Set where

data OneStatePriceImpliesNationalWeightedPricePermission : Set where

data NationalProductionImpliesNationalSavingsPermission : Set where

data LargerHeadlineImpliesImprovedBiologicalEfficacyPermission : Set where

paperModelDoesNotAutoFix2024Parameters :
  PaperModelImpliesSame2024ParametersPermission → ⊥
paperModelDoesNotAutoFix2024Parameters ()

oneStatePriceDoesNotAutoPromoteToNationalWeightedPrice :
  OneStatePriceImpliesNationalWeightedPricePermission → ⊥
oneStatePriceDoesNotAutoPromoteToNationalWeightedPrice ()

nationalProductionDoesNotAutoPromoteToNationalSavings :
  NationalProductionImpliesNationalSavingsPermission → ⊥
nationalProductionDoesNotAutoPromoteToNationalSavings ()

largerHeadlineDoesNotAutoPromoteToImprovedBiologicalEfficacy :
  LargerHeadlineImpliesImprovedBiologicalEfficacyPermission → ⊥
largerHeadlineDoesNotAutoPromoteToImprovedBiologicalEfficacy ()

------------------------------------------------------------------------
-- Existing boundaries imported rather than re-proved semantically.
------------------------------------------------------------------------

paper2019_2020AvoidedCost = Model2023.avoidedUreaCostIs15200MillionUSD
headlineCalculationReplayOpen = Headline.calculationReplayStillOpen
historicalSavingsLawNotUniversal =
  EconX.historicalFitDoesNotAutoPromoteToUniversalFutureSavingsLaw
