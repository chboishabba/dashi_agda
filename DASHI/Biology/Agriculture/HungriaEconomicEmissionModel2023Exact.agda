module DASHI.Biology.Agriculture.HungriaEconomicEmissionModel2023Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SOURCE-EXACT ECONOMIC / EMISSIONS PRODUCER
--
-- External source:
--   Tiago Santos Telles; Marco Antonio Nogueira; Mariangela Hungria
--   "Economic value of biological nitrogen fixation in soybean crops in Brazil"
--   Environmental Technology & Innovation 31 (2023) 103158
--   DOI 10.1016/j.eti.2023.103158
--
-- Source-owned 2019-2020 results include:
--   * avoided urea cost value of BNF: USD 15.2 billion;
--   * inoculation + coinoculation profit: USD 914 million;
--   * coinoculation adoption: 25% of Brazilian soybean area;
--   * estimated mitigation from replacing N fertilizer by BNF:
--       183 million Mg CO2-e.
--
-- DASHI owns the typed reconstruction and the promotion boundaries below;
-- these datatypes/theorems are not attributed to the paper's authors.
------------------------------------------------------------------------

data ModelCoordinate : Set where
  soybeanYield : ModelCoordinate
  nitrogenExtractionPerGrain : ModelCoordinate
  secondaryNitrogenSupply : ModelCoordinate
  fertilizerRecoveryEfficiency : ModelCoordinate
  soybeanArea : ModelCoordinate
  ureaNitrogenPrice : ModelCoordinate
  emissionCoefficient : ModelCoordinate

data ProducerKind : Set where
  observedRegionalInput literatureAssumption accountingCoefficient computedOutput : ProducerKind

record ModelInputLineage : Set where
  constructor modelInputLineage
  field
    coordinate : ModelCoordinate
    producerKind : ProducerKind
    sourceReference : String
    yearIndexed : Bool
    regionIndexed : Bool

open ModelInputLineage public

------------------------------------------------------------------------
-- Equation (1) lineage.  The paper computes avoided cost from the equivalent
-- urea-N required in the absence of BNF.  It assumes soybean N demand of
-- 80 kg N per 1000 kg grain, fertilizer-N recovery of 50%, and subtracts
-- 30 kg N/ha from secondary sources before valuing the urea-equivalent N.
------------------------------------------------------------------------

soybeanYieldLineage : ModelInputLineage
soybeanYieldLineage =
  modelInputLineage soybeanYield observedRegionalInput
    "CONAB state/year soybean yield data, 2009-2010 through 2019-2020"
    true true

nitrogenExtractionLineage : ModelInputLineage
nitrogenExtractionLineage =
  modelInputLineage nitrogenExtractionPerGrain literatureAssumption
    "Hungria and Mendes 2015: 80 kg N per 1000 kg soybean grain"
    false false

secondaryNitrogenLineage : ModelInputLineage
secondaryNitrogenLineage =
  modelInputLineage secondaryNitrogenSupply literatureAssumption
    "Paper assumption: 30 kg N/ha supplied by soil organic matter plus MAP/DAP-associated N"
    false false

fertilizerEfficiencyLineage : ModelInputLineage
fertilizerEfficiencyLineage =
  modelInputLineage fertilizerRecoveryEfficiency literatureAssumption
    "Paper adopts 50% N-fertilizer recovery, from reported 30-50% range"
    false false

soybeanAreaLineage : ModelInputLineage
soybeanAreaLineage =
  modelInputLineage soybeanArea observedRegionalInput
    "CONAB state/year soybean cultivated-area data"
    true true

ureaPriceLineage : ModelInputLineage
ureaPriceLineage =
  modelInputLineage ureaNitrogenPrice observedRegionalInput
    "CONAB state/year prices paid for N fertilizer; urea assumed at 46% N"
    true true

emissionCoefficientLineage : ModelInputLineage
emissionCoefficientLineage =
  modelInputLineage emissionCoefficient accountingCoefficient
    "Paper uses 10 kg CO2-e per kg N fertilizer when synthesis and transportation are included, citing IPCC 2006 context"
    false false

------------------------------------------------------------------------
-- Exact published 2019-2020 outputs, represented in integer source units.
------------------------------------------------------------------------

record Published2019_2020Outputs : Set where
  constructor publishedOutputs
  field
    avoidedUreaCostMillionUSD : Nat
    inoculationCoinoculationProfitMillionUSD : Nat
    coinoculationPercentOfSoybeanArea : Nat
    mitigatedCO2eMillionMg : Nat

open Published2019_2020Outputs public

paper2019_2020Outputs : Published2019_2020Outputs
paper2019_2020Outputs = publishedOutputs 15200 914 25 183

avoidedUreaCostIs15200MillionUSD :
  avoidedUreaCostMillionUSD paper2019_2020Outputs ≡ 15200
avoidedUreaCostIs15200MillionUSD = refl

profitIs914MillionUSD :
  inoculationCoinoculationProfitMillionUSD paper2019_2020Outputs ≡ 914
profitIs914MillionUSD = refl

coinoculationAreaIs25Percent :
  coinoculationPercentOfSoybeanArea paper2019_2020Outputs ≡ 25
coinoculationAreaIs25Percent = refl

mitigationIs183MillionMg :
  mitigatedCO2eMillionMg paper2019_2020Outputs ≡ 183
mitigationIs183MillionMg = refl

------------------------------------------------------------------------
-- Same-object/version firewall against the 2025 retrospective headline.
--
-- The World Food Prize / Embrapa 2025 material reports approximately
-- USD 25 billion/year and >230 million tonnes CO2-e for 2024-era adoption.
-- Those are not the literal 2019-2020 outputs of this 2023 paper.
------------------------------------------------------------------------

paper2023MitigationEquals2025Headline230 :
  mitigatedCO2eMillionMg paper2019_2020Outputs ≡ 230 → ⊥
paper2023MitigationEquals2025Headline230 ()

paper2023AvoidedCostEquals2025Headline25000 :
  avoidedUreaCostMillionUSD paper2019_2020Outputs ≡ 25000 → ⊥
paper2023AvoidedCostEquals2025Headline25000 ()

record VersionedHeadlineBoundary : Set where
  constructor versionedHeadlineBoundary
  field
    paperResultHasCropSeason : Bool
    paperResultHasCropSeasonIsTrue : paperResultHasCropSeason ≡ true
    laterHeadlineMayReuseModelFamily : Bool
    laterHeadlineMayReuseModelFamilyIsTrue : laterHeadlineMayReuseModelFamily ≡ true
    laterHeadlineIsDefinitionallySameOutput : Bool
    laterHeadlineIsDefinitionallySameOutputIsFalse : laterHeadlineIsDefinitionallySameOutput ≡ false
    extrapolationFrom2019_2020To2024Closed : Bool
    extrapolationFrom2019_2020To2024ClosedIsFalse : extrapolationFrom2019_2020To2024Closed ≡ false

canonicalVersionedHeadlineBoundary : VersionedHeadlineBoundary
canonicalVersionedHeadlineBoundary =
  versionedHeadlineBoundary true refl true refl false refl false refl
