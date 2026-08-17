module DASHI.Governance.MeasuredSituatedChoiceReceiptExact where

------------------------------------------------------------------------
-- MEASURED SITUATED-CHOICE RECEIPTS
--
-- This module begins the transition from illustrative Nat choice geometry to
-- source-attached measured observations.  Measurements remain metric-specific:
-- a Healthy Food Basket percentage is not silently identified with a generic
-- grocery-price percentage, and a remote-vs-district comparison is not silently
-- identified with remote-vs-capital-city comparison.
--
-- SOURCES / BOUNDED ROLES
--
-- Northern Territory Department of Health,
-- "2019 NT Market Basket Survey", approved 23 June 2020,
-- TRM EDOC2019/416260; no DOI asserted.
-- Primary report.  Executive summary: average Healthy Food Basket (HFB) in
-- remote stores was 56% more expensive than district-centre supermarkets;
-- Current Diet Basket (CDB) was 40% more expensive.  Table 8 reports average
-- HFB $848 remote vs $542 district-centre supermarket and CDB $913 vs $650.
--
-- Northern Territory Government,
-- "NT Market Basket Survey 2023", published 5 June 2024; no DOI asserted.
-- Official dataset.  A 2026 systematic scoping review reports the NT 2023
-- remote/district healthy-food-basket differential as 40%, citing this dataset.
-- This file therefore marks the 2023 40% value as secondary extraction from an
-- official primary dataset until the exact primary table is separately parsed.
--
-- Megan Ferguson; Kerin O'Dea; Mark Chatfield; Marjory Moodie; Jon Altman;
-- Julie Brimblecombe,
-- "The comparative cost of food and beverages at remote Indigenous
-- communities, Northern Territory, Australia", Australian and New Zealand
-- Journal of Public Health 40:S21-S26 (2016),
-- DOI 10.1111/1753-6405.12370.
-- Bounded role: cross-sectional 20-store comparison; 443 products representing
-- 63% of food/beverage expenditure were on average 60% above Darwin advertised
-- supermarket prices and 68% above Adelaide advertised prices.  Different
-- metric/comparator from the NT HFB series.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record MeasurementSource : Set where
  constructor measurementSource
  field
    authorsOrInstitution : String
    title : String
    venueOrIdentifier : String
    year : Nat
    doi : String
    boundedRole : String

open MeasurementSource public

data MeasurementMetric : Set where
  healthyFoodBasketGap : MeasurementMetric
  currentDietBasketGap : MeasurementMetric
  purchasedProductPriceGap : MeasurementMetric

data Comparator : Set where
  remoteVsDistrictSupermarket : Comparator
  remoteVsDarwinAdvertised : Comparator
  remoteVsAdelaideAdvertised : Comparator

data ReceiptDirectness : Set where
  primaryDirect : ReceiptDirectness
  secondaryExtractionOfPrimaryDataset : ReceiptDirectness
  peerReviewedPrimaryStudy : ReceiptDirectness

record PercentGapReceipt : Set where
  constructor percentGapReceipt
  field
    source : MeasurementSource
    metric : MeasurementMetric
    comparator : Comparator
    observationYear : Nat
    percentHigher : Nat
    directness : ReceiptDirectness
    causalAttributionInstalled : Bool

open PercentGapReceipt public

nt2019Source : MeasurementSource
nt2019Source = measurementSource
  "Northern Territory Department of Health"
  "2019 NT Market Basket Survey"
  "TRM EDOC2019/416260; approved 23 June 2020"
  2020
  "no DOI asserted"
  "primary repeated market-basket report; remote vs district-centre price/availability comparison"

nt2023Source : MeasurementSource
nt2023Source = measurementSource
  "Northern Territory Government, Department of Health"
  "NT Market Basket Survey 2023"
  "NT Government Open Data; published 5 June 2024"
  2024
  "no DOI asserted"
  "official dataset; exact 40% value here is retained as secondary extraction pending direct primary-table receipt"

ferguson2016Source : MeasurementSource
ferguson2016Source = measurementSource
  "Megan Ferguson; Kerin O'Dea; Mark Chatfield; Marjory Moodie; Jon Altman; Julie Brimblecombe"
  "The comparative cost of food and beverages at remote Indigenous communities, Northern Territory, Australia"
  "Australian and New Zealand Journal of Public Health 40:S21-S26"
  2016
  "10.1111/1753-6405.12370"
  "20 remote NT stores; 443 purchased products; remote vs advertised Darwin/Adelaide supermarket prices"

nt2019HealthyFoodBasket56 : PercentGapReceipt
nt2019HealthyFoodBasket56 = percentGapReceipt
  nt2019Source healthyFoodBasketGap remoteVsDistrictSupermarket
  2019 56 primaryDirect false

nt2019CurrentDietBasket40 : PercentGapReceipt
nt2019CurrentDietBasket40 = percentGapReceipt
  nt2019Source currentDietBasketGap remoteVsDistrictSupermarket
  2019 40 primaryDirect false

nt2023HealthyFoodBasket40 : PercentGapReceipt
nt2023HealthyFoodBasket40 = percentGapReceipt
  nt2023Source healthyFoodBasketGap remoteVsDistrictSupermarket
  2023 40 secondaryExtractionOfPrimaryDataset false

fergusonRemoteVsDarwin60 : PercentGapReceipt
fergusonRemoteVsDarwin60 = percentGapReceipt
  ferguson2016Source purchasedProductPriceGap remoteVsDarwinAdvertised
  2015 60 peerReviewedPrimaryStudy false

fergusonRemoteVsAdelaide68 : PercentGapReceipt
fergusonRemoteVsAdelaide68 = percentGapReceipt
  ferguson2016Source purchasedProductPriceGap remoteVsAdelaideAdvertised
  2015 68 peerReviewedPrimaryStudy false

------------------------------------------------------------------------
-- Metric/comparator discipline.
------------------------------------------------------------------------

data SamePercentPromotesSameMetric : Set where

data PriceGapPromotesFreightShare : Set where

data PriceGapPromotesCompetitionShare : Set where

data RepeatedObservationPromotesCausalTrend : Set where

samePercentDoesNotPromoteSameMetric : SamePercentPromotesSameMetric → ⊥
samePercentDoesNotPromoteSameMetric ()

priceGapDoesNotPromoteFreightShare : PriceGapPromotesFreightShare → ⊥
priceGapDoesNotPromoteFreightShare ()

priceGapDoesNotPromoteCompetitionShare : PriceGapPromotesCompetitionShare → ⊥
priceGapDoesNotPromoteCompetitionShare ()

repeatedObservationDoesNotPromoteCausalTrend :
  RepeatedObservationPromotesCausalTrend → ⊥
repeatedObservationDoesNotPromoteCausalTrend ()

record MeasuredSituatedChoiceBoundary : Set where
  constructor measuredSituatedChoiceBoundary
  field
    measuredRemotePriceGapInstalled : Bool
    repeatedHFBObservationsInstalled : Bool
    everyObservationDirectPrimaryTable : Bool
    metricIdentityRequiredForComparison : Bool
    priceGapEqualsFreightCausalShare : Bool
    priceGapEqualsCompetitionCausalShare : Bool
    quantitativeReceiptEqualsCoercion : Bool

canonicalMeasuredSituatedChoiceBoundary : MeasuredSituatedChoiceBoundary
canonicalMeasuredSituatedChoiceBoundary =
  measuredSituatedChoiceBoundary true true false true false false false
