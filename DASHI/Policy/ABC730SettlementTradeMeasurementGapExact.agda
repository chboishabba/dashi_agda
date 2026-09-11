module DASHI.Policy.ABC730SettlementTradeMeasurementGapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact as Obligation
import DASHI.Policy.ABC730PalestinianIncidenceSnowballExact as Incidence

------------------------------------------------------------------------
-- Measurement wall for destination-specific settlement trade.
--
-- Ordinary country-code trade aggregates cannot be silently treated as a
-- settlement-origin exposure denominator when the official statistics do not
-- identify settlement goods as a separate reporting category.
------------------------------------------------------------------------

data MeasurementStatus : Set where
  directlyObserved : MeasurementStatus
  boundedAggregateOnly : MeasurementStatus
  notSeparatelyIdentified : MeasurementStatus
  modelRequired : MeasurementStatus

record TradeMeasurementReceipt : Set where
  constructor tradeMeasurementReceipt
  field
    receiptId : String
    source : Source.AttributedSource
    deweyParent : String
    stableSourceId : String
    targetQuantity : String
    status : MeasurementStatus
    boundedFinding : String
    residual : String

open TradeMeasurementReceipt public

ukParliament2025Source : Source.AttributedSource
ukParliament2025Source = Source.mkNoDOISource
  "HM Treasury / UK Parliament written answer"
  "UK trade with Israeli settlements in the Occupied Palestinian Territories"
  "UK Parliament written question 45543"
  "2025"
  "https://questions-statements.parliament.uk/written-questions/detail/2025-04-17/45543/"
  Source.governmentSource
  "primary official answer describing what settlement-origin trade quantities UK customs statistics can and cannot identify"
  Source.publicAttribution

ukSettlementValueNotSeparatelyIdentified : TradeMeasurementReceipt
ukSettlementValueNotSeparatelyIdentified = tradeMeasurementReceipt
  "ABC730-measurement:uk-settlement-value-not-separate"
  ukParliament2025Source
  "382.7"
  "UKParliament:written-question:45543:2025-04-24"
  "value and volume of UK imports/exports specifically attributable to Israeli settlements"
  notSeparatelyIdentified
  "The official answer says trade statistics use partner country codes Israel (IL) or Occupied Palestinian Territories/Palestine (PS), rather than a separate settlement trade category."
  "Origin verification can distinguish particular goods for customs treatment, but ordinary published partner-country aggregates do not pay the total settlement-origin trade value."

commonsLibrary2026Source : Source.AttributedSource
commonsLibrary2026Source = Source.mkNoDOISource
  "House of Commons Library"
  "UK trade with Israeli settlements in the Occupied Palestinian Territories: Government statements and guidance in 2026"
  "House of Commons Library research briefing CBP-10945"
  "2026"
  "https://commonslibrary.parliament.uk/research-briefings/cbp-10945/"
  Source.institutionalSource
  "parliamentary research briefing consolidating official guidance and the trade-measurement limitation"
  Source.publicAttribution

ukAggregateBoundOnly : TradeMeasurementReceipt
ukAggregateBoundOnly = tradeMeasurementReceipt
  "ABC730-measurement:uk-aggregate-bound-only"
  commonsLibrary2026Source
  "382.7"
  "UKCommonsLibrary:CBP-10945"
  "settlement-origin component of UK-Palestine/UK-Israel recorded trade"
  boundedAggregateOnly
  "The briefing records that accurate UK trade figures for the settlements are difficult to obtain; broader UK-Palestine and UK-Israel totals are not a same-object measure of settlement goods."
  "A settlement-specific exposure estimate requires additional origin-level customs data, firm/product reconstruction, or a transparent model with uncertainty bounds."

record SettlementTradeMeasurementState : Set where
  constructor settlementTradeMeasurementState
  field
    settlementOriginCanBeCheckedForIndividualGoods : Bool
    publishedCountryAggregateSeparatesSettlements : Bool
    totalIsraelTradeCanPaySettlementExposure : Bool
    totalPalestineTradeCanPaySettlementExposure : Bool
    firmOrOriginLevelReconstructionRequired : Bool
    uncertaintyMustBeRetained : Bool

canonicalSettlementTradeMeasurementState : SettlementTradeMeasurementState
canonicalSettlementTradeMeasurementState =
  settlementTradeMeasurementState true false false false true true

------------------------------------------------------------------------
-- Consequence for the C029 magnitude/counterfactual obligations.
------------------------------------------------------------------------

data AggregateSubstitutionPaysMagnitude : Set where
aggregateSubstitutionDoesNotPayMagnitude : AggregateSubstitutionPaysMagnitude → ⊥
aggregateSubstitutionDoesNotPayMagnitude ()

data CountryCodeEqualsSettlementOrigin : Set where
countryCodeDoesNotEqualSettlementOrigin : CountryCodeEqualsSettlementOrigin → ⊥
countryCodeDoesNotEqualSettlementOrigin ()

data DifficultMeasurementMeansZeroExposure : Set where
difficultMeasurementDoesNotMeanZeroExposure : DifficultMeasurementMeansZeroExposure → ⊥
difficultMeasurementDoesNotMeanZeroExposure ()

counterfactualAnchor : Obligation.PolicyEffectObligation
counterfactualAnchor = Obligation.counterfactualComparison

incidenceFrontierAnchor : Incidence.PalestinianIncidenceFrontier
incidenceFrontierAnchor = Incidence.canonicalPalestinianIncidenceFrontier
