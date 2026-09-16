module DASHI.Policy.ABC730FirmDestinationExposureSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Policy.ABC730PalestinianIncidenceSnowballExact as Incidence
import DASHI.Policy.ABC730SettlementTradeMeasurementGapExact as Measurement
import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Snowball

------------------------------------------------------------------------
-- Firm -> destination -> worker exposure snowball.
--
-- This owner records candidate firm/destination evidence without pretending
-- that a settlement-business list is an export register or that an export
-- document establishes Palestinian worker incidence.
------------------------------------------------------------------------

data FirmExposureEvidenceClass : Set where
  primaryUNBusinessDatabase : FirmExposureEvidenceClass
  investigativeExportDocumentAnalysis : FirmExposureEvidenceClass
  historicalFirmExportList : FirmExposureEvidenceClass
  destinationAggregate : FirmExposureEvidenceClass

data FirmExposurePayment : Set where
  settlementBusinessCandidatePaid : FirmExposurePayment
  settlementExportCandidatePaid : FirmExposurePayment
  originMisclassificationRiskPaid : FirmExposurePayment
  exactDestinationExposureUnpaid : FirmExposurePayment
  workerFirmWeldUnpaid : FirmExposurePayment
  workerDestinationWeldUnpaid : FirmExposurePayment
  consequenceMagnitudeUnpaid : FirmExposurePayment

record FirmExposureReceipt : Set where
  constructor firmExposureReceipt
  field
    receiptId : String
    source : Source.AttributedSource
    deweyParent : String
    stableIdentifier : String
    evidenceClass : FirmExposureEvidenceClass
    payment : FirmExposurePayment
    boundedFinding : String
    residual : String

open FirmExposureReceipt public

ohchr2025Source : Source.AttributedSource
ohchr2025Source = Source.mkNoDOISource
  "Office of the United Nations High Commissioner for Human Rights"
  "Database of business enterprises involved in activities related to Israeli settlements"
  "UN Human Rights Office / A-HRC-60-19"
  "2025"
  "https://www.un.org/unispal/document/business-database-26sep25/"
  Source.institutionalSource
  "primary UN-mandated database update identifying enterprises involved in specified settlement-related activities"
  Source.publicAttribution

ohchrBusinessCandidateReceipt : FirmExposureReceipt
ohchrBusinessCandidateReceipt = firmExposureReceipt
  "ABC730-firm:ohchr-business-database-2025"
  ohchr2025Source
  "338.7"
  "UN:A-HRC-60-19:2025-09-26"
  primaryUNBusinessDatabase
  settlementBusinessCandidatePaid
  "The UN Human Rights Office 2025 update lists 158 business enterprises from 11 countries involved in specified settlement-related activities."
  "Inclusion identifies a settlement-related business candidate. It does not establish that the enterprise exports goods to Australia or the UK, employs Palestinian workers, or would be directly affected by the announced goods ban."

globalEchoSource : Source.AttributedSource
globalEchoSource = Source.mkNoDOISource
  "Emma Graham-Harrison and Lorenzo Tondo reporting on Global Echo Litigation Center document analysis"
  "Settler products from occupied Palestine sold to Europe as Israeli, investigation finds"
  "The Guardian / underlying Global Echo investigation"
  "2026"
  "https://www.theguardian.com/world/2026/jun/15/settler-products-from-occupied-palestine-sold-to-europe-as-israeli-investigation-finds"
  Source.newsSource
  "secondary reporting of export-document analysis relevant to settlement-origin classification and evasion risk"
  Source.publicAttribution

originMisclassificationReceipt : FirmExposureReceipt
originMisclassificationReceipt = firmExposureReceipt
  "ABC730-firm:origin-misclassification-europe-2026"
  globalEchoSource
  "382.7"
  "guardian:2026-06-15:settler-products-export-documents"
  investigativeExportDocumentAnalysis
  originMisclassificationRiskPaid
  "The reported investigation analysed more than 30,000 export documents and found settlement-origin agricultural products among Europe-bound shipments, with a substantial subset reported as mislabelled as Israeli-grown."
  "This pays origin-misclassification/evasion as a real implementation risk in the Europe-bound sample. It does not establish the Australian rate, the total settlement export value, or worker incidence."

historicalUKFirmSource : Source.AttributedSource
historicalUKFirmSource = Source.mkNoDOISource
  "UK economic-links investigation"
  "Report: UK economic links with Israeli settlements"
  "historical civil-society investigation"
  "2009"
  "https://electronicintifada.net/content/report-uk-economic-links-israeli-settlements/3423"
  Source.namedSourceKind "civil-society investigation"
  "historical candidate list of settlement-linked companies reported as exporting to the UK; discovery aid only"
  Source.publicAttribution

historicalFirmCandidateReceipt : FirmExposureReceipt
historicalFirmCandidateReceipt = firmExposureReceipt
  "ABC730-firm:historical-uk-exporter-candidates"
  historicalUKFirmSource
  "382.7"
  "historical:uk-settlement-exporter-list:2009"
  historicalFirmExportList
  settlementExportCandidatePaid
  "The historical report identifies named settlement-linked firms reported as exporting categories including produce, wine, cosmetics, plastics, metals and textiles to the UK."
  "The list is old, secondary and not sufficient for 2026 payment. Each firm needs current same-company, same-site and destination receipts before use in the live counterfactual."

record FirmDestinationWorkerState : Set where
  constructor firmDestinationWorkerState
  field
    settlementBusinessUniversePartiallyIdentified : Bool
    exportOriginEvasionRiskObserved : Bool
    currentUKDestinationFirmSetPaid : Bool
    currentAustraliaDestinationFirmSetPaid : Bool
    firmProductVolumePaid : Bool
    firmPalestinianWorkerCountPaid : Bool
    workerExportDestinationDependencePaid : Bool
    policyMagnitudePaid : Bool

canonicalFirmDestinationWorkerState : FirmDestinationWorkerState
canonicalFirmDestinationWorkerState =
  firmDestinationWorkerState true true false false false false false false

record FirmDestinationFrontier : Set where
  constructor firmDestinationFrontier
  field
    currentFirmIdentity : String
    productionSiteIdentity : String
    productOrigin : String
    destinationMarket : String
    shipmentVolume : String
    PalestinianWorkerCount : String
    workerFunction : String
    revenueOrOutputDependence : String
    substitutionPath : String
    sameFirmHistoricalContinuityRequired : Bool

canonicalFirmDestinationFrontier : FirmDestinationFrontier
canonicalFirmDestinationFrontier = firmDestinationFrontier
  "resolve current legal entity and ownership for each candidate enterprise"
  "pay the exact settlement/industrial-zone/farm production site rather than company-level adjacency"
  "pay origin for the particular goods/services entering the policy scope"
  "pay UK and Australian destination receipts separately"
  "quantify affected shipment/value volume with uncertainty retained"
  "obtain primary or high-quality current worker count by paid production site"
  "separate Palestinian workers performing production from unrelated company/site employment"
  "estimate what share of the worker-supported output/revenue depends on the sanctioned destination"
  "test diversion, relabelling, reallocation, Palestinian substitution and business closure pathways"
  true

data UNDatabaseMeansExporter : Set where
unDatabaseDoesNotMeanExporter : UNDatabaseMeansExporter → ⊥
unDatabaseDoesNotMeanExporter ()

data ExporterMeansPalestinianEmployer : Set where
exporterDoesNotMeanPalestinianEmployer : ExporterMeansPalestinianEmployer → ⊥
exporterDoesNotMeanPalestinianEmployer ()

data MislabelledShipmentPaysTotalTradeMagnitude : Set where
mislabelledShipmentDoesNotPayTotalTradeMagnitude : MislabelledShipmentPaysTotalTradeMagnitude → ⊥
mislabelledShipmentDoesNotPayTotalTradeMagnitude ()

data HistoricalFirmIdentityAutomaticallyCurrent : Set where
historicalFirmIdentityDoesNotAutomaticallyCurrent : HistoricalFirmIdentityAutomaticallyCurrent → ⊥
historicalFirmIdentityDoesNotAutomaticallyCurrent ()

incidenceFrontierAnchor : Incidence.PalestinianIncidenceFrontier
incidenceFrontierAnchor = Incidence.canonicalPalestinianIncidenceFrontier

measurementStateAnchor : Measurement.SettlementTradeMeasurementState
measurementStateAnchor = Measurement.canonicalSettlementTradeMeasurementState

snowballBoundaryAnchor : Snowball.SnowballAttributionBoundary
snowballBoundaryAnchor = Snowball.canonicalSnowballAttributionBoundary
