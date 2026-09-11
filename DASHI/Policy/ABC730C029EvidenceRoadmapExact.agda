module DASHI.Policy.ABC730C029EvidenceRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Attribution
import DASHI.Policy.ABC730C029IbrahimSourceAtlasExact as Atlas
import DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact as Obligation
import DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact as Mechanism
import DASHI.Policy.ABC730PalestinianIncidenceSnowballExact as Palestinian
import DASHI.Policy.ABC730SettlementTradeMeasurementGapExact as Measurement
import DASHI.Policy.ABC730AustralianImplementationSnowballExact as Australia
import DASHI.Policy.ABC730AustralianOriginBaselineExact as Origin
import DASHI.Policy.ABC730FirmDestinationExposureSnowballExact as Firm

------------------------------------------------------------------------
-- Thin composition owner for the C029 evidence roadmap.
------------------------------------------------------------------------

data RoadmapStatus : Set where
  paid : RoadmapStatus
  partial : RoadmapStatus
  open : RoadmapStatus
  blockedByMeasurement : RoadmapStatus
  downstream : RoadmapStatus

data C029RoadmapCoordinate : Set where
  transcriptObjectIdentity : C029RoadmapCoordinate
  speakerAttribution : C029RoadmapCoordinate
  ibrahimSourceCoordinates : C029RoadmapCoordinate
  statedRationale : C029RoadmapCoordinate
  affectedClassesNamed : C029RoadmapCoordinate
  ukInstrumentIdentity : C029RoadmapCoordinate
  ukOriginDifferentiation : C029RoadmapCoordinate
  australianTargetedAlternative : C029RoadmapCoordinate
  targetedComplianceBurden : C029RoadmapCoordinate
  australianOriginComplianceBaseline : C029RoadmapCoordinate
  settlementSubcountryClassifier : C029RoadmapCoordinate
  palestinianSettlementEmploymentExposure : C029RoadmapCoordinate
  settlementBusinessCandidateUniverse : C029RoadmapCoordinate
  originMisclassificationRisk : C029RoadmapCoordinate
  settlementTradeMagnitude : C029RoadmapCoordinate
  australianBlanketImplementationCost : C029RoadmapCoordinate
  australianBusinessMateriality : C029RoadmapCoordinate
  palestinianDestinationWorkerLinkage : C029RoadmapCoordinate
  palestinianNetIncidence : C029RoadmapCoordinate
  israeliNetIncidence : C029RoadmapCoordinate
  targetedVsBlanketCounterfactual : C029RoadmapCoordinate
  gaslightingEvaluativeAptness : C029RoadmapCoordinate

record RoadmapEntry : Set where
  constructor roadmapEntry
  field
    coordinate : C029RoadmapCoordinate
    status : RoadmapStatus
    ownerReference : String
    nextPayment : String

open RoadmapEntry public

transcriptIdentityEntry : RoadmapEntry
transcriptIdentityEntry = roadmapEntry transcriptObjectIdentity paid
  "DASHI.Policy.ABC730IbrahimSnowballAttributionExact"
  "none; preserve URL+SHA and claim-relative primaryness"

speakerAttributionEntry : RoadmapEntry
speakerAttributionEntry = roadmapEntry speakerAttribution paid
  "DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact"
  "none for C030-C033; do not reopen from parser ambiguity"

ibrahimAtlasEntry : RoadmapEntry
ibrahimAtlasEntry = roadmapEntry ibrahimSourceCoordinates paid
  "DASHI.Policy.ABC730C029IbrahimSourceAtlasExact"
  "continue append-only enrichment of QID/DOI/stable-ID/link coordinates without importing claim truth"

statedRationaleEntry : RoadmapEntry
statedRationaleEntry = roadmapEntry statedRationale paid
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "none for the fact that Wong stated implementation/unintended-consequence concerns"

affectedClassesEntry : RoadmapEntry
affectedClassesEntry = roadmapEntry affectedClassesNamed paid
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "Australian businesses, Palestinians and Israelis are named; mechanisms remain separate"

ukInstrumentEntry : RoadmapEntry
ukInstrumentEntry = roadmapEntry ukInstrumentIdentity paid
  "DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact"
  "track final implementing legislation and customs guidance when enacted"

ukOriginEntry : RoadmapEntry
ukOriginEntry = roadmapEntry ukOriginDifferentiation paid
  "DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact"
  "none for existence of UK origin differentiation; Australia-specific transfer remains open"

australianTargetedEntry : RoadmapEntry
australianTargetedEntry = roadmapEntry australianTargetedAlternative paid
  "DASHI.Policy.ABC730AustralianImplementationSnowballExact"
  "keep current sanctions list/revision as execution evidence"

targetedComplianceEntry : RoadmapEntry
targetedComplianceEntry = roadmapEntry targetedComplianceBurden paid
  "DASHI.Policy.ABC730AustralianImplementationSnowballExact"
  "quantify burden only for the comparative cost consumer"

originBaselineEntry : RoadmapEntry
originBaselineEntry = roadmapEntry australianOriginComplianceBaseline paid
  "DASHI.Policy.ABC730AustralianOriginBaselineExact"
  "country-level import declarations/origin advice/food origin labelling are established baseline capabilities"

settlementClassifierEntry : RoadmapEntry
settlementClassifierEntry = roadmapEntry settlementSubcountryClassifier open
  "DASHI.Policy.ABC730AustralianOriginBaselineExact"
  "pay legal test, production-location evidence, declaration field/process, exemptions, importer burden, customs systems burden and enforcement error for settlement-place origin"

palestinianExposureEntry : RoadmapEntry
palestinianExposureEntry = roadmapEntry palestinianSettlementEmploymentExposure paid
  "DASHI.Policy.ABC730PalestinianIncidenceSnowballExact"
  "worker/site/industry cross-tabs and household-dependence data"

businessUniverseEntry : RoadmapEntry
businessUniverseEntry = roadmapEntry settlementBusinessCandidateUniverse partial
  "DASHI.Policy.ABC730FirmDestinationExposureSnowballExact"
  "current firm/site/product/destination weld; OHCHR business database is not an export register"

misclassificationEntry : RoadmapEntry
misclassificationEntry = roadmapEntry originMisclassificationRisk partial
  "DASHI.Policy.ABC730FirmDestinationExposureSnowballExact"
  "Australian or instrument-specific rate and enforcement response"

tradeMagnitudeEntry : RoadmapEntry
tradeMagnitudeEntry = roadmapEntry settlementTradeMagnitude blockedByMeasurement
  "DASHI.Policy.ABC730SettlementTradeMeasurementGapExact"
  "origin-level customs data, firm/product reconstruction, or transparent model with uncertainty"

australianImplementationCostEntry : RoadmapEntry
australianImplementationCostEntry = roadmapEntry australianBlanketImplementationCost open
  "DASHI.Policy.ABC730AustralianImplementationSnowballExact"
  "DFAT/ABF/Treasury/Attorney-General advice or released impact assessment specifying incremental settlement-specific costs"

australianBusinessEntry : RoadmapEntry
australianBusinessEntry = roadmapEntry australianBusinessMateriality open
  "DASHI.Policy.ABC730AustralianImplementationSnowballExact"
  "importer/product exposure, incremental due-diligence cost, customs classification burden and materiality"

workerDestinationEntry : RoadmapEntry
workerDestinationEntry = roadmapEntry palestinianDestinationWorkerLinkage open
  "DASHI.Policy.ABC730FirmDestinationExposureSnowballExact"
  "firm -> site -> product -> destination -> Palestinian worker -> output/revenue dependence"

palestinianNetEntry : RoadmapEntry
palestinianNetEntry = roadmapEntry palestinianNetIncidence open
  "DASHI.Policy.ABC730PalestinianIncidenceSnowballExact"
  "employment loss/reallocation, Palestinian producer substitution and household-income counterfactual"

israeliNetEntry : RoadmapEntry
israeliNetEntry = roadmapEntry israeliNetIncidence open
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "identify which Israelis are claimed to be harmed, mechanism, sign, and whether settlers/green-line producers/consumers are conflated"

counterfactualEntry : RoadmapEntry
counterfactualEntry = roadmapEntry targetedVsBlanketCounterfactual open
  "DASHI.Policy.ABC730AustralianImplementationSnowballExact"
  "compare incremental compliance cost, coverage, evasion, substitution and expected settlement-support reduction"

gaslightingEntry : RoadmapEntry
gaslightingEntry = roadmapEntry gaslightingEvaluativeAptness downstream
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "evaluate only after protective-rationale mechanism/evidence and instrument counterfactual are paid"

record C029RoadmapSummary : Set where
  constructor c029RoadmapSummary
  field
    transcriptAndAttributionComplete : Bool
    ibrahimAttributionSurfaceComplete : Bool
    policyObjectIdentityComplete : Bool
    mechanismCandidateLayerComplete : Bool
    australianOriginBaselineComplete : Bool
    settlementSpecificOriginDesignComplete : Bool
    consequenceMagnitudeComplete : Bool
    australianImplementationEvidenceComplete : Bool
    distributionalIncidenceComplete : Bool
    comparativeInstrumentEvidenceComplete : Bool
    evaluativeConsumerReady : Bool
    currentBottleneck : String
    shortestNextPath : String

canonicalC029RoadmapSummary : C029RoadmapSummary
canonicalC029RoadmapSummary = c029RoadmapSummary
  true true true true true false false false false false false
  "settlement-specific origin design/cost plus firm-destination-worker linkage"
  "pay Australian settlement-place origin implementation evidence and current firm->site->product->destination->worker exposure before net consequence or evaluative aptness"

------------------------------------------------------------------------
-- Anchors ensure this dashboard composes rather than forks the owners.
------------------------------------------------------------------------

attributionAnchor : Attribution.SnowballAttributionBoundary
attributionAnchor = Attribution.canonicalSnowballAttributionBoundary

atlasAnchor : Atlas.AtlasBoundary
atlasAnchor = Atlas.canonicalAtlasBoundary

obligationAnchor : Obligation.PolicyEvaluationRoadmap
obligationAnchor = Obligation.canonicalPolicyEvaluationRoadmap

mechanismAnchor : Mechanism.SnowballFrontier
mechanismAnchor = Mechanism.canonicalSnowballFrontier

palestinianAnchor : Palestinian.PalestinianConsequenceState
palestinianAnchor = Palestinian.canonicalPalestinianConsequenceState

measurementAnchor : Measurement.SettlementTradeMeasurementState
measurementAnchor = Measurement.canonicalSettlementTradeMeasurementState

australiaAnchor : Australia.ComparativeComplianceState
australiaAnchor = Australia.canonicalComparativeComplianceState

originAnchor : Origin.AustralianOriginCapabilityState
originAnchor = Origin.canonicalAustralianOriginCapabilityState

firmAnchor : Firm.FirmDestinationWorkerState
firmAnchor = Firm.canonicalFirmDestinationWorkerState
