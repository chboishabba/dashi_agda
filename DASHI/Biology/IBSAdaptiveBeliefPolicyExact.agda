module DASHI.Biology.IBSAdaptiveBeliefPolicyExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.IBSCausalMaintenanceRegimeExact as Regime
import DASHI.Biology.IBSMonashAdaptiveSequencingExact as Monash
import DASHI.Biology.IBSMonashLongHorizonAdaptiveExact as Long
import DASHI.Biology.IBSTrialDesignDonorAtlasExact as Donor
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- QUALITATIVE BELIEF / POLICY SURFACE
--
-- This module deliberately does not manufacture probabilities, likelihoods,
-- utilities, or a patient-specific clinical recommendation.  It states what a
-- future validated adaptive policy must retain and what evidence may update.
------------------------------------------------------------------------

data BeliefLevel : Set where
  unsupportedCandidate : BeliefLevel
  unresolvedCandidate : BeliefLevel
  comparativelyElevatedCandidate : BeliefLevel
  comparativelyDowngradedCandidate : BeliefLevel

data BeliefAuthority : Set where
  structuralBeliefOnly : BeliefAuthority
  observationConditionedBelief : BeliefAuthority
  perturbationConditionedBelief : BeliefAuthority
  validatedPosteriorModel : BeliefAuthority

record IBSRegimeBeliefState : Set where
  constructor ibs-regime-belief-state
  field
    microbialImmune : BeliefLevel
    barrierSensory : BeliefLevel
    autonomicCentral : BeliefLevel
    bileAcidMotility : BeliefLevel
    mixedCoupled : BeliefLevel
    authority : BeliefAuthority
    populationReference : String
    historyReference : String
    numericProbabilityAssigned : Bool
    clinicalDiagnosisClaimed : Bool
open IBSRegimeBeliefState public

canonicalInitialIBSBeliefState : IBSRegimeBeliefState
canonicalInitialIBSBeliefState = ibs-regime-belief-state
  unresolvedCandidate unresolvedCandidate unresolvedCandidate
  unresolvedCandidate unresolvedCandidate structuralBeliefOnly
  "no participant-specific population instantiated"
  "no participant-specific history instantiated"
  false false

data ObservationKind : Set where
  symptomTrajectoryObservation : ObservationKind
  proximalTargetEngagementObservation : ObservationKind
  competingFibreObservation : ObservationKind
  challengeRecoveryObservation : ObservationKind
  burdenSafetyObservation : ObservationKind
  negativeTargetingValidationObservation : ObservationKind

record PolicyObservation : Set where
  constructor policy-observation
  field
    kind : ObservationKind
    sourceOrExperimentReference : String
    actionReference : String
    observedSurface : String
    timingReference : String
    targetEngagementReference : String
    competingFibreReference : String
    burdenSafetyReference : String
    carryoverReference : String
    causalInterpretationClaimed : Bool
open PolicyObservation public

data UpdateDirection : Set where
  noDirectionalUpdate : UpdateDirection
  comparativelyRaiseCandidate : UpdateDirection
  comparativelyLowerCandidate : UpdateDirection
  reopenCompetingCandidates : UpdateDirection

data UpdateAuthority : Set where
  designOnlyUpdate : UpdateAuthority
  associationConditionedUpdate : UpdateAuthority
  perturbationConditionedUpdate : UpdateAuthority
  externallyValidatedUpdate : UpdateAuthority

record BeliefUpdateReceipt : Set where
  constructor belief-update-receipt
  field
    before : IBSRegimeBeliefState
    observation : PolicyObservation
    candidate : Regime.MaintenanceRegimeCandidate
    direction : UpdateDirection
    updateAuthority : UpdateAuthority
    likelihoodOrDecisionRuleReference : String
    alternativeExplanationReference : String
    afterReference : String
    createsRegimeTruth : Bool
    createsDiagnosis : Bool
open BeliefUpdateReceipt public

-- A valid update requires an explicit interpretation contract; no generic
-- Bayes arithmetic is invented in this module.
record BeliefUpdateObligation : Set where
  constructor belief-update-obligation
  field
    responseDefinitionPredeclared : Bool
    timingPredeclared : Bool
    proximalTargetEngagementMeasured : Bool
    competingFibresRetained : Bool
    adherenceExposureRetained : Bool
    carryoverWashoutAudited : Bool
    burdenSafetyRetained : Bool
    alternativeExplanationsRetained : Bool
    likelihoodModelValidatedIfNumericPosteriorUsed : Bool
open BeliefUpdateObligation public

canonicalBeliefUpdateObligation : BeliefUpdateObligation
canonicalBeliefUpdateObligation = belief-update-obligation
  true true true true true true true true true

data ClinicalValueClass : Set where
  establishedOrGuidelineValue : ClinicalValueClass
  boundedClinicalValue : ClinicalValueClass
  experimentalProbeValue : ClinicalValueClass

data InformationValueClass : Set where
  lowInformationValue : InformationValueClass
  singleFibreInformation : InformationValueClass
  orthogonalFibreInformation : InformationValueClass
  transitionHistoryInformation : InformationValueClass

data SafetyStatus : Set where
  establishedSafetyContext : SafetyStatus
  requiresScreening : SafetyStatus
  experimentalSafetyUncertain : SafetyStatus

data CarryoverRisk : Set where
  lowCarryoverRisk : CarryoverRisk
  explicitWashoutNeeded : CarryoverRisk
  longOrUnknownCarryover : CarryoverRisk

record AdaptivePolicyAction : Set where
  constructor adaptive-policy-action
  field
    actionReference : String
    clinicalValue : ClinicalValueClass
    informationValue : InformationValueClass
    burden : Monash.BurdenClass
    safety : SafetyStatus
    carryover : CarryoverRisk
    proximalReadout : String
    distalReadout : String
    foodQoLReference : String
    accessReference : String
    stopOrSwitchReference : String
open AdaptivePolicyAction public

lowFODMAPPolicyAction : AdaptivePolicyAction
lowFODMAPPolicyAction = adaptive-policy-action
  "Monash low-FODMAP / personalized reintroduction family"
  establishedOrGuidelineValue orthogonalFibreInformation Monash.moderateBurden
  requiresScreening explicitWashoutNeeded
  "exposure/adherence + fermentation/luminal ecology where measured"
  "symptom/QOL trajectory"
  "LongHorizonAdaptive: minimize unnecessary restriction and retain food-related QoL"
  "dietitian access and implementation burden retained"
  "switch/reintroduce according to prospectively defined symptom, nutrition and burden rules"

blindedChallengePolicyAction : AdaptivePolicyAction
blindedChallengePolicyAction = adaptive-policy-action
  "blinded FODMAP-class challenge / mechanistically matched rescue"
  experimentalProbeValue transitionHistoryInformation Monash.moderateBurden
  requiresScreening explicitWashoutNeeded
  "class-specific provocation/rescue timing"
  "symptom recurrence and recovery"
  "challenge burden retained; not intended as indefinite restriction"
  "requires standardized challenge materials and monitoring"
  "stop for unacceptable symptoms/safety or after predeclared discrimination target is met"

digitalGDHPolicyAction : AdaptivePolicyAction
digitalGDHPolicyAction = adaptive-policy-action
  "digital gut-directed hypnotherapy family"
  boundedClinicalValue orthogonalFibreInformation Monash.lowBurden
  establishedSafetyContext longOrUnknownCarryover
  "central/interoceptive/autonomic change where actually measured"
  "symptom and quality-of-life trajectory"
  "no dietary restriction burden"
  "digital delivery can reduce access burden relative to therapist-only delivery"
  "evaluate at predeclared programme milestones; response does not identify CNS-only regime"

quailProbePolicyAction : AdaptivePolicyAction
quailProbePolicyAction = adaptive-policy-action
  "quail-egg mast-cell candidate probe"
  experimentalProbeValue singleFibreInformation Monash.moderateBurden
  experimentalSafetyUncertain explicitWashoutNeeded
  "mast-cell/histamine/tryptase and exposure confirmation"
  "whole-system symptom/barrier/metabolome/autonomic trajectory"
  "food exposure and allergy burden retained"
  "requires quail-specific allergy screening and controlled preparation"
  "no clinical sequencing until a human IBS same-object experiment exists"

canonicalAdaptivePolicyActionAtlas : List AdaptivePolicyAction
canonicalAdaptivePolicyActionAtlas =
  lowFODMAPPolicyAction ∷ blindedChallengePolicyAction ∷
  digitalGDHPolicyAction ∷ quailProbePolicyAction ∷ []

data PolicyStoppingReason : Set where
  therapeuticGoalMet : PolicyStoppingReason
  burdenOrSafetyDominates : PolicyStoppingReason
  discriminationTargetMet : PolicyStoppingReason
  carryoverPreventsInterpretation : PolicyStoppingReason
  noAdmissibleNextAction : PolicyStoppingReason
  externalValidationRequired : PolicyStoppingReason

record AdaptivePolicyDecision : Set where
  constructor adaptive-policy-decision
  field
    currentBeliefReference : String
    admissibleActions : List AdaptivePolicyAction
    selectedActionReference : String
    selectionRationale : String
    predeclaredSwitchRule : String
    stoppingReasonIfAny : PolicyStoppingReason
    numericOptimizationClaimed : Bool
    patientSpecificRecommendationClaimed : Bool
open AdaptivePolicyDecision public

data SingleResponseMakesRegimeTruePermission : Set where
singleResponseDoesNotMakeRegimeTrue : SingleResponseMakesRegimeTruePermission → ⊥
singleResponseDoesNotMakeRegimeTrue ()

data InformationOptimalActionIsClinicalOptimalPermission : Set where
informationOptimalDoesNotMeanClinicalOptimal : InformationOptimalActionIsClinicalOptimalPermission → ⊥
informationOptimalDoesNotMeanClinicalOptimal ()

data PostHocSwitchEqualsProspectiveAdaptivePolicyPermission : Set where
postHocSwitchDoesNotEqualProspectiveAdaptivePolicy : PostHocSwitchEqualsProspectiveAdaptivePolicyPermission → ⊥
postHocSwitchDoesNotEqualProspectiveAdaptivePolicy ()

data BeliefStateIsClinicalDiagnosisPermission : Set where
beliefStateDoesNotBecomeClinicalDiagnosis : BeliefStateIsClinicalDiagnosisPermission → ⊥
beliefStateDoesNotBecomeClinicalDiagnosis ()

data NumericPosteriorWithoutValidatedLikelihoodPermission : Set where
numericPosteriorRequiresValidatedLikelihood : NumericPosteriorWithoutValidatedLikelihoodPermission → ⊥
numericPosteriorRequiresValidatedLikelihood ()

record AdaptivePolicyBoundary : Set where
  constructor adaptive-policy-boundary
  field
    regimeBeliefsRemainHypotheses : Bool
    therapeuticAndInformationValueSeparated : Bool
    burdenQoLAccessSafetyRetained : Bool
    switchingRulesMustBeProspective : Bool
    negativeEvidenceCanDowngradeCandidate : Bool
    numericPosteriorInvented : Bool
    numericUtilityInvented : Bool
    patientSpecificRecommendationMade : Bool
    donorBoundary : Donor.TrialDesignDonorBoundary
    longHorizonBoundary : Long.MonashLongHorizonBoundary

canonicalAdaptivePolicyBoundary : AdaptivePolicyBoundary
canonicalAdaptivePolicyBoundary = adaptive-policy-boundary
  true true true true true false false false
  Donor.canonicalTrialDesignDonorBoundary
  Long.canonicalMonashLongHorizonBoundary

record AdaptivePolicyParetoNode : Set where
  constructor adaptive-policy-pareto-node
  field
    label : String
    route : Snowball.DiscoveryRoute
    paidReference : String
    residual : String
    nextAcquisition : String
    authorityBoundary : String
open AdaptivePolicyParetoNode public

canonicalAdaptivePolicyParetoFrontier : List AdaptivePolicyParetoNode
canonicalAdaptivePolicyParetoFrontier =
  adaptive-policy-pareto-node
    "prospective SMART IBS policy" Snowball.experimentalDesign
    "SMART methodology donor plus current IBS orthogonal treatment evidence"
    "no IBS-validated response state, rerandomization rule, or distal utility function"
    "pilot SMART with low-burden first-line options and preregistered stage-2 choices for non/partial responders"
    "prospective design evaluates a policy; it does not reveal a true regime label by fiat" ∷
  adaptive-policy-pareto-node
    "Bayesian adaptive N-of-1 policy" Snowball.experimentalDesign
    "Senarathne 2020 design donor + IBS crossover/challenge evidence"
    "likelihood, carryover and prior structure are not validated for heterogeneous IBS actions"
    "begin with reversible short-latency challenge/rescue actions; prevalidate carryover and stopping model"
    "no numeric posterior is admitted before its likelihood/model is validated" ∷
  adaptive-policy-pareto-node
    "minimal-effective restriction policy" Snowball.experimentalDesign
    "Monash long-horizon burden evidence + 2026 external personalized-FODMAP trial"
    "optimal reintroduction/switch timing remains unvalidated"
    "randomized policy trial comparing protocolized personalized reintroduction against usual dietetic care"
    "food-QoL/nutritional burden are co-primary decision coordinates, not afterthoughts" ∷
  adaptive-policy-pareto-node
    "mechanistic targeting validation gate" Snowball.externalKnowledgeComparison
    "Balsiger 2026 negative CLE targeting trial"
    "many candidate biomarkers still lack sham-controlled treatment-selection validation"
    "do not admit a biomarker into the policy as a targeting rule until prospective guided-vs-sham/usual selection improves a relevant outcome"
    "mechanistic signal and actionable treatment selector are separate claims" ∷
  adaptive-policy-pareto-node
    "quail candidate admission" Snowball.experimentalDesign
    "preclinical quail ladder + human non-IBS oral exposure + independent IBS mast-cell/histamine mechanisms"
    "human IBS same-object target-engagement and safety evidence absent"
    "first-in-IBS controlled exposure study before any adaptive-policy branch is clinically admissible"
    "candidate information value does not create treatment authority" ∷ []
