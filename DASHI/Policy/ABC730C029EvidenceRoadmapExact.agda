module DASHI.Policy.ABC730C029EvidenceRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
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
import DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact as LegalFabric

------------------------------------------------------------------------
-- Thin composition owner for the C029 evidence roadmap.
--
-- The legal-machinery hyperfabric is a structural interpretation layer, not a
-- new evidence source.  `paid` below therefore means the representation/gate
-- machinery exists and is wired, not that its open empirical gates are paid.
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
  legalMachineryConsumerFabric : C029RoadmapCoordinate
  statedRationale : C029RoadmapCoordinate
  affectedClassesNamed : C029RoadmapCoordinate
  ukInstrumentIdentity : C029RoadmapCoordinate
  ukOriginDifferentiation : C029RoadmapCoordinate
  australianTargetedAlternative : C029RoadmapCoordinate
  targetedComplianceBurden : C029RoadmapCoordinate
  australianOriginComplianceBaseline : C029RoadmapCoordinate
  settlementSubcountryClassifier : C029RoadmapCoordinate
  adviceDecisionLineage : C029RoadmapCoordinate
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

legalMachineryEntry : RoadmapEntry
legalMachineryEntry = roadmapEntry legalMachineryConsumerFabric paid
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "structural layer paid: WrongType, non-factorability, advice-atom lineage, cutset, admissible transitions and consumer hyperfabric are wired; empirical gates remain independently open"

statedRationaleEntry : RoadmapEntry
statedRationaleEntry = roadmapEntry statedRationale paid
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "none for the fact that Wong stated implementation/unintended-consequence concerns"

affectedClassesEntry : RoadmapEntry
affectedClassesEntry = roadmapEntry affectedClassesNamed paid
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "Australian businesses, Palestinians and Israelis are named; situated mechanisms remain separate"

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
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "first cutset residual: pay the settlement-place legal test, production-location evidence, declaration field/process, exemptions, importer/customs burden and error/evasion semantics"

adviceLineageEntry : RoadmapEntry
adviceLineageEntry = roadmapEntry adviceDecisionLineage open
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "after acquiring DFAT/ABF/Treasury advice, atomise exact propositions and close same-object transports departmental analysis -> ministerial brief -> public rationale -> decision"

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
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "do not factor through flat affected-class label; pay worker loss/reallocation, Palestinian producer substitution and household-income counterfactual"

israeliNetEntry : RoadmapEntry
israeliNetEntry = roadmapEntry israeliNetIncidence open
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "identify which Israelis are claimed to be harmed, mechanism, sign, and whether settlers/green-line producers/consumers are conflated"

counterfactualEntry : RoadmapEntry
counterfactualEntry = roadmapEntry targetedVsBlanketCounterfactual open
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "only compare incremental compliance cost, coverage, evasion, substitution and expected settlement-support reduction once the representation is admissible and consumer-adequate"

gaslightingEntry : RoadmapEntry
gaslightingEntry = roadmapEntry gaslightingEvaluativeAptness downstream
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "admissible transition is disabled until settlement classifier, incidence and comparative-instrument gates are paid"

record C029RoadmapSummary : Set where
  constructor c029RoadmapSummary
  field
    transcriptAndAttributionComplete : Bool
    ibrahimAttributionSurfaceComplete : Bool
    legalConsumerFabricComplete : Bool
    policyObjectIdentityComplete : Bool
    mechanismCandidateLayerComplete : Bool
    australianOriginBaselineComplete : Bool
    settlementSpecificOriginDesignComplete : Bool
    adviceDecisionLineageComplete : Bool
    consequenceMagnitudeComplete : Bool
    australianImplementationEvidenceComplete : Bool
    distributionalIncidenceComplete : Bool
    comparativeInstrumentEvidenceComplete : Bool
    evaluativeConsumerReady : Bool
    currentFirstResidual : LegalFabric.C029CutsetResidual
    currentBottleneck : String
    shortestNextPath : String

canonicalC029RoadmapSummary : C029RoadmapSummary
canonicalC029RoadmapSummary = c029RoadmapSummary
  true true true true true true false false false false false false false
  (LegalFabric.firstC029Residual LegalFabric.canonicalC029Cutset)
  "settlement-specific origin classifier first; then same-object advice lineage plus firm-destination-worker incidence"
  "pay the settlement-place classifier/application gate; acquire and atomise Australian advice; then close situated firm->destination->worker and Israeli/Palestinian incidence before comparative or evaluative promotion"

currentRoadmapResidualIsSettlementClassifier :
  C029RoadmapSummary.currentFirstResidual canonicalC029RoadmapSummary ≡
  LegalFabric.settlementClassifierResidual
currentRoadmapResidualIsSettlementClassifier =
  LegalFabric.currentFirstResidualIsSettlementClassifier

------------------------------------------------------------------------
-- Anchors ensure this dashboard composes rather than forks the owners.
------------------------------------------------------------------------

attributionAnchor : Attribution.SnowballAttributionBoundary
attributionAnchor = Attribution.canonicalSnowballAttributionBoundary

atlasAnchor : Atlas.AtlasBoundary
atlasAnchor = Atlas.canonicalAtlasBoundary

legalCutsetAnchor : LegalFabric.C029LegalEvidenceCutset
legalCutsetAnchor = LegalFabric.canonicalC029Cutset

legalTransitionAnchor : DASHI.Core.AdmissibleTransitionHyperfabricExact.AdmissibleTransitionSystem
legalTransitionAnchor = LegalFabric.c029AdmissibleTransitionSystem

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
