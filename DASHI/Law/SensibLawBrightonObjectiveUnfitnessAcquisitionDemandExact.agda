module DASHI.Law.SensibLawBrightonObjectiveUnfitnessAcquisitionDemandExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BoundAcquisitionDemandExact as Bound
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as Diligence
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- BRIGHTON OBJECTIVE-UNFITNESS: EXACT SOURCE ACQUISITION DEMAND
--
-- The direct historical s 185(3)(a) compiler is already ready.  Its only live
-- evidence input is objective unfitness at the 24 January 2023 evaluation time.
--
-- Reviewed private carriers establish that:
--   * Job #13812 "Urgent mould" was assigned after initial owner approval;
--   * an external mould inspection occurred;
--   * a second quote/inspection workflow existed;
--   * the contractor later confirmed it inspected for Ray White but refused to
--     disclose the client's report to the tenant;
--   * the agent subsequently described a larger issue requiring extensive
--     attention and issued a non-liveability Form 12.
--
-- What is NOT in hand is the contractor's actual report/quote findings.  This
-- module binds acquisition to that exact missing source rather than asking for
-- more repetitions of the agent's characterization.
------------------------------------------------------------------------

data ObjectiveUnfitnessRequirement : Set where
  acquireOriginalMouldInspectionReport : ObjectiveUnfitnessRequirement
  authenticateSamePremisesInspection : ObjectiveUnfitnessRequirement
  extractExactContractorFindings : ObjectiveUnfitnessRequirement
  classifyFindingsAgainstFitToLiveElement : ObjectiveUnfitnessRequirement

requirementGap : ObjectiveUnfitnessRequirement → Diligence.SourceDiligenceGap
requirementGap acquireOriginalMouldInspectionReport = Diligence.primarySourceNotSearched
requirementGap authenticateSamePremisesInspection = Diligence.sameObjectUnresolved
requirementGap extractExactContractorFindings = Diligence.propositionSupportUnresolved
requirementGap classifyFindingsAgainstFitToLiveElement = Diligence.applicabilityOpen

requiredProducer : ObjectiveUnfitnessRequirement → Search.ProducerClass
requiredProducer r = Diligence.producerForSourceDiligenceGap (requirementGap r)

record ObjectiveUnfitnessAcquisition : Set where
  constructor objective-unfitness-acquisition
  field
    targetRequirement : ObjectiveUnfitnessRequirement
    targetGap : Diligence.SourceDiligenceGap
    producer : Search.ProducerClass
    acquisitionReference : String

open ObjectiveUnfitnessAcquisition public

acquisitionGap : ObjectiveUnfitnessAcquisition → Diligence.SourceDiligenceGap
acquisitionGap = targetGap

acquisitionProducer : ObjectiveUnfitnessAcquisition → Search.ProducerClass
acquisitionProducer = producer

objectiveUnfitnessAcquisitionAlignment :
  Bound.AcquisitionAlignment
    ObjectiveUnfitnessRequirement
    Diligence.SourceDiligenceGap
    Search.ProducerClass
    ObjectiveUnfitnessAcquisition
objectiveUnfitnessAcquisitionAlignment = Bound.acquisition-alignment
  requirementGap
  requiredProducer
  acquisitionGap
  acquisitionProducer

originalContractorReportAcquisition : ObjectiveUnfitnessAcquisition
originalContractorReportAcquisition = objective-unfitness-acquisition
  acquireOriginalMouldInspectionReport
  Diligence.primarySourceNotSearched
  Search.propositionSourceProducer
  "Acquire the original Natural Mould Removal / MouldMen inspection report and quote commissioned for 17 Gordon St Brighton after Job #13812, preserving report date, inspected premises, observations, measurements, conclusions, remediation scope and provenance"

currentObjectiveUnfitnessDemand :
  Bound.BoundAcquisitionDemand
    objectiveUnfitnessAcquisitionAlignment
    acquireOriginalMouldInspectionReport
    Diligence.primarySourceNotSearched
currentObjectiveUnfitnessDemand = Bound.bound-acquisition-demand
  originalContractorReportAcquisition
  refl
  refl
  refl

currentDemandPaysExactResidual :
  Bound.acquisitionResidual objectiveUnfitnessAcquisitionAlignment
    (Bound.acquisition currentObjectiveUnfitnessDemand)
  ≡ requirementGap acquireOriginalMouldInspectionReport
currentDemandPaysExactResidual =
  Bound.acquisitionPaysSelectedResidual currentObjectiveUnfitnessDemand

currentDemandUsesExactProducer :
  Bound.acquisitionProducer objectiveUnfitnessAcquisitionAlignment
    (Bound.acquisition currentObjectiveUnfitnessDemand)
  ≡ requiredProducer acquireOriginalMouldInspectionReport
currentDemandUsesExactProducer =
  Bound.acquisitionUsesSelectedProducer currentObjectiveUnfitnessDemand

------------------------------------------------------------------------
-- Current evidence state and promotion firewall.
------------------------------------------------------------------------

record ObjectiveUnfitnessAcquisitionState : Set where
  constructor objective-unfitness-acquisition-state
  field
    contractorInspectionExistenceConfirmed : Bool
    contractorReportInHand : Bool
    exactContractorFindingsInHand : Bool
    objectiveUnfitnessClassificationPaid : Bool
    sourceReference : String

canonicalObjectiveUnfitnessAcquisitionState : ObjectiveUnfitnessAcquisitionState
canonicalObjectiveUnfitnessAcquisitionState =
  objective-unfitness-acquisition-state
    true
    false
    false
    false
    "MouldMen 13-Feb-2023 confirms inspection for Ray White but declines disclosure; original report/quote absent from reviewed Gmail corpus"

data InspectionExistencePaysReportContent : Set where
data AgentSummaryPaysContractorFinding : Set where
data ReportAcquisitionAutomaticallyPaysObjectiveUnfitness : Set where

inspectionExistenceDoesNotPayReportContent :
  InspectionExistencePaysReportContent → ⊥
inspectionExistenceDoesNotPayReportContent ()

agentSummaryDoesNotPayContractorFinding :
  AgentSummaryPaysContractorFinding → ⊥
agentSummaryDoesNotPayContractorFinding ()

reportAcquisitionDoesNotAutoPayObjectiveUnfitness :
  ReportAcquisitionAutomaticallyPaysObjectiveUnfitness → ⊥
reportAcquisitionDoesNotAutoPayObjectiveUnfitness ()

------------------------------------------------------------------------
-- Proof-directed search intent: acquire the missing primary artifact first.
------------------------------------------------------------------------

currentObjectiveUnfitnessSearchIntent : Search.SearchIntent
currentObjectiveUnfitnessSearchIntent = Search.searchIntent
  "SensibLawBrightonS185ViolationElementFrontierExact.objectiveUnfitnessElementReference"
  "obtain the original contractor inspection/quote findings for 17 Gordon St Brighton and test whether those findings support the exact historical s185(3)(a) fit-to-live element at 24 January 2023"
  Search.propositionSourceProducer
  Search.exploitKnownResidual
  "17 Gordon St, Brighton QLD 4017"
  "5 December 2022 through 24 January 2023"
  Search.primaryTextRequired
  "contractor inspection existence, agent summaries, Form 12 ground and photographs remain separate evidence fibres until the original report is acquired and same-object authenticated"
  "Job #13812 assignment; 20-Jan delay thread; 24-Jan agent larger-issue/non-liveability statement; 13-Feb MouldMen inspection confirmation/refusal"
  "original contractor report or quote must preserve inspected address, inspection date, author/company, observations, measurements if any, conclusions and recommended remediation"
  "exclude generic mould guidance, later summaries and repeated tenant/agent assertions; do not promote report acquisition itself into objective legal unfitness without evaluating the actual findings"
  (Search.searchBudget 6 12 3 "primary contractor report first; stop once original findings are acquired or their unavailability is independently established")
  "Brighton objective-unfitness primary contractor-source acquisition intent"
