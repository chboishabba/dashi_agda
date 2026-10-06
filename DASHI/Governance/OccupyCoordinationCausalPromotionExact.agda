module DASHI.Governance.OccupyCoordinationCausalPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- OCCUPY INCIDENCE -> BURDEN CAUSAL-PROMOTION FRONTIER.
--
-- This is DASHI-derived methodology, not an Occupy-source claim.
--
-- Repo donor pattern:
-- DASHI.Promotion.ChemistryBiologyObligations requires, for causal promotion,
-- a declared causal graph / structural equations, intervention or equivalent
-- identification surface, confound boundary, estimand-to-observable map,
-- uncertainty policy and sensitivity analysis.  This owner specializes that
-- promotion pattern to the governance evidence lane without importing biology
-- semantics or claiming that the current archive identifies a causal effect.
------------------------------------------------------------------------

data CausalNode : Set where
  trueParticipationIncidence : CausalNode
  observedArchivalIncidence : CausalNode
  participantCount : CausalNode
  issueCount : CausalNode
  meetingType : CausalNode
  externalShock : CausalNode
  sourceCompleteness : CausalNode
  repeatedParticipantStructure : CausalNode
  coordinationBurden : CausalNode


data EdgeStatus : Set where
  candidateStructuralHypothesis : EdgeStatus
  measurementProcessHypothesis : EdgeStatus

record CandidateCausalEdge : Set where
  constructor candidateCausalEdge
  field
    from : CausalNode
    to : CausalNode
    status : EdgeStatus
    rationale : String

open CandidateCausalEdge public

------------------------------------------------------------------------
-- Candidate graph only.  These arrows are proposed for identification design;
-- they are not empirical results and do not become true merely by appearing
-- here.
------------------------------------------------------------------------

candidateCausalGraph : List CandidateCausalEdge
candidateCausalGraph =
  candidateCausalEdge participantCount trueParticipationIncidence candidateStructuralHypothesis
    "more participants can change the opportunity surface for participant-issue interactions; effect not assumed monotone"
  ∷ candidateCausalEdge issueCount trueParticipationIncidence candidateStructuralHypothesis
    "more distinct issues can change the opportunity surface for interaction; effect not assumed monotone"
  ∷ candidateCausalEdge participantCount coordinationBurden candidateStructuralHypothesis
    "participant count is a required control because it can affect burden independently of observed incidence"
  ∷ candidateCausalEdge issueCount coordinationBurden candidateStructuralHypothesis
    "issue count is a required control because it can affect burden independently of observed incidence"
  ∷ candidateCausalEdge meetingType coordinationBurden candidateStructuralHypothesis
    "meeting type / procedural format can affect burden and must not be silently absorbed into incidence"
  ∷ candidateCausalEdge externalShock coordinationBurden candidateStructuralHypothesis
    "raids, relocation, policing, weather, deadlines or other external shocks may affect burden independently"
  ∷ candidateCausalEdge repeatedParticipantStructure coordinationBurden candidateStructuralHypothesis
    "repeated-person dependence across meetings may affect outcomes and uncertainty"
  ∷ candidateCausalEdge trueParticipationIncidence coordinationBurden candidateStructuralHypothesis
    "target causal relation to be identified rather than assumed"
  ∷ candidateCausalEdge trueParticipationIncidence observedArchivalIncidence measurementProcessHypothesis
    "archive coding observes only source-explicit interactions and can miss true participation"
  ∷ candidateCausalEdge sourceCompleteness observedArchivalIncidence measurementProcessHypothesis
    "source completeness affects how much of the underlying participation relation is observable"
  ∷ []

------------------------------------------------------------------------
-- Promotion requirements.
------------------------------------------------------------------------

record CausalPromotionRequirements : Set where
  constructor causalPromotionRequirements
  field
    requiresDeclaredCausalGraph : Bool
    requiresStructuralOrIdentificationModel : Bool
    requiresIdentificationCriterion : Bool
    requiresConfoundSelectionBoundary : Bool
    requiresEstimandObservableMap : Bool
    requiresEffectSizeUncertaintyPolicy : Bool
    requiresSensitivityAnalysis : Bool
    requiresSourceCompletenessModel : Bool
    requiresRepeatedParticipantDependenceModel : Bool
    requiresProspectiveHeldOutValidation : Bool
    requiresDatasetChecksumAndCodingReceipt : Bool

open CausalPromotionRequirements public

canonicalCausalPromotionRequirements : CausalPromotionRequirements
canonicalCausalPromotionRequirements =
  causalPromotionRequirements
    true true true true true true true true true true true

record CausalPromotionBoundary : Set where
  constructor causalPromotionBoundary
  field
    candidateGraphIsEmpiricalCausalGraph : Bool
    archivalCooccurrenceIdentifiesEffect : Bool
    externalExperimentalPlausibilityIdentifiesOccupyEffect : Bool
    oneIncidenceDurationPairIdentifiesSlope : Bool
    retrospectiveSplitCountsAsProspectiveValidation : Bool

    incidenceBurdenCausalEffectPromoted : Bool
    empiricalCoordinationCostFunctionalPromoted : Bool

open CausalPromotionBoundary public

canonicalCausalPromotionBoundary : CausalPromotionBoundary
canonicalCausalPromotionBoundary =
  causalPromotionBoundary
    false
    false
    false
    false
    false
    false
    false

record CurrentCausalPromotionBlockers : Set where
  constructor currentCausalPromotionBlockers
  field
    missingCompleteIncidence : Bool
    missingDurationForMostMeetings : Bool
    missingMediationDuration : Bool
    missingCompleteControlMatrix : Bool
    missingSourceCompletenessModel : Bool
    missingIdentificationProof : Bool
    missingEffectUncertaintyModel : Bool
    missingSensitivityAnalysis : Bool
    missingProspectiveHeldOutReceipt : Bool

open CurrentCausalPromotionBlockers public

canonicalCurrentCausalPromotionBlockers : CurrentCausalPromotionBlockers
canonicalCurrentCausalPromotionBlockers =
  currentCausalPromotionBlockers
    true true true true true true true true true

canonicalOccupyCoordinationCausalPromotionReceipt : GenericReceipt.GenericReceipt
canonicalOccupyCoordinationCausalPromotionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy incidence-to-burden causal-promotion frontier"
    "DASHI.Governance.OccupyCoordinationCausalPromotionExact"
    "canonicalCausalPromotionBoundary"
    "specializes the repo's existing causal-promotion obligation pattern to a candidate governance graph separating true incidence, observed archival incidence, participant/issue controls, meeting type, external shocks, source completeness, repeated participants and coordination burden"
    "the candidate graph is DASHI experiment design rather than source truth; current archival co-occurrence, one incidence-duration pair and external group-decision experiments do not identify an Occupy causal effect, and promotion remains blocked pending identification, uncertainty, sensitivity, completeness and prospective held-out receipts"
    "agda -i . DASHI/Governance/OccupyCoordinationCausalPromotionRegression.agda"
