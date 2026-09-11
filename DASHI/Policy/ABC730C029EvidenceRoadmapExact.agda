module DASHI.Policy.ABC730C029EvidenceRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Attribution
import DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact as Obligation
import DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact as Mechanism
import DASHI.Policy.ABC730PalestinianIncidenceSnowballExact as Palestinian
import DASHI.Policy.ABC730SettlementTradeMeasurementGapExact as Measurement
import DASHI.Policy.ABC730AustralianImplementationSnowballExact as Australia
import DASHI.Policy.ABC730FirmDestinationExposureSnowballExact as Firm

------------------------------------------------------------------------
-- Thin composition owner for the C029 evidence roadmap.
-- No new planner, scoring function or source authority is introduced here.
-- Existing owners remain authoritative for their own receipts.
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
  statedRationale : C029RoadmapCoordinate
  affectedClassesNamed : C029RoadmapCoordinate
  ukInstrumentIdentity : C029RoadmapCoordinate
  ukOriginDifferentiation : C029RoadmapCoordinate
  australianTargetedAlternative : C029RoadmapCoordinate
  targetedComplianceBurden : C029RoadmapCoordinate
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
  "quantify burden only if a comparative cost consumer requires it"

palestinianExposureEntry : RoadmapEntry
palestinianExposureEntry = roadmapEntry palestinianSettlementEmploymentExposure paid
  "DASHI.Policy.ABC730PalestinianIncidenceSnowballExact"
  "worker/site/industry cross-tabs and household-dependence data"

businessUniverseEntry : RoadmapEntry
businessUniverseEntry = roadmapEntry settlementBusinessCandidateUniverse partial
  "DASHI.Policy.ABC730FirmDestinationExposureSnowballExact"
  "current firm/site/product/destination weld for candidates; UN database is not an export register"

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
  "DFAT/ABF/Treasury/Attorney-General advice or released impact assessment specifying incremental costs"

australianBusinessEntry : RoadmapEntry
australianBusinessEntry = roadmapEntry australianBusinessMateriality open
  "DASHI.Policy.ABC730AustralianImplementationSnowballExact"
  "importer/product exposure, due-diligence cost, customs classification burden and materiality"

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
  "identify which Israelis are claimed to be harmed, by what mechanism, and whether settlers/green-line producers/consumers are being conflated"

counterfactualEntry : RoadmapEntry
counterfactualEntry = roadmapEntry targetedVsBlanketCounterfactual open
  "DASHI.Policy.ABC730AustralianImplementationSnowballExact"
  "compare coverage, administrative cost, evasion risk, substitution and expected settlement-support reduction"

gaslightingEntry : RoadmapEntry
gaslightingEntry = roadmapEntry gaslightingEvaluativeAptness downstream
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "evaluate only after protective-rationale mechanism/evidence and instrument counterfactual are paid"

record C029RoadmapSummary : Set where
  constructor c029RoadmapSummary
  field
    transcriptAndAttributionComplete : Bool
    policyObjectIdentityComplete : Bool
    mechanismCandidateLayerComplete : Bool
    consequenceMagnitudeComplete : Bool
    australianImplementationEvidenceComplete : Bool
    distributionalIncidenceComplete : Bool
    comparativeInstrumentEvidenceComplete : Bool
    evaluativeConsumerReady : Bool
    currentBottleneck : String
    shortestNextPath : String

canonicalC029RoadmapSummary : C029RoadmapSummary
canonicalC029RoadmapSummary = c029RoadmapSummary
  true
  true
  true
  false
  false
  false
  false
  false
  "firm/destination/worker linkage plus Australia-specific incremental implementation and business-incidence evidence"
  "pay Australian DFAT/ABF/Treasury implementation analysis and current firm->site->product->destination->worker exposure before attempting net consequence or gaslighting aptness"

------------------------------------------------------------------------
-- Anchors ensure this dashboard composes rather than forks the owners.
------------------------------------------------------------------------

attributionAnchor : Attribution.SnowballAttributionBoundary
attributionAnchor = Attribution.canonicalSnowballAttributionBoundary

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

firmAnchor : Firm.FirmDestinationWorkerState
firmAnchor = Firm.canonicalFirmDestinationWorkerState
