module DASHI.Cognition.ClinicToStreetsFormulationExperimentExact where

open import DASHI.Core.Prelude

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Core.ITIRInvestigationAcquisitionParetoExact as INV
import DASHI.Cognition.ClinicToStreetsIntersectionalityReuseExact as Intersectionality
import DASHI.Cognition.ClinicToStreetsSOTAEvidenceAtlasExact as SOTA

------------------------------------------------------------------------
-- CLINIC-TO-STREETS FORMULATION EXPERIMENT
--
-- The testable target is weaker and cleaner than "therapy is
-- counterinsurgency": whether adding a structurally relevant coordinate to an
-- otherwise matched formulation changes a declared downstream decision/action
-- consumer.  This owner reuses the existing robust-experiment and acquisition
-- Pareto machinery; it does not introduce a new experiment or ranking ontology.
------------------------------------------------------------------------

data FormulationArm : Set where
  atomisedArm : FormulationArm
  contextualArm : FormulationArm

data CaseClass : Set where
  structuralCoordinateRelevant : CaseClass
  structuralCoordinateIrrelevantControl : CaseClass

data FormulationOutcome : Set where
  causalAttributionOutcome : FormulationOutcome
  selfBlameOutcome : FormulationOutcome
  individualTreatmentRecommendationOutcome : FormulationOutcome
  materialSocialReferralOutcome : FormulationOutcome
  representedIndividualActionOutcome : FormulationOutcome
  representedCollectiveActionOutcome : FormulationOutcome
  confidenceOutcome : FormulationOutcome
  allianceAcceptabilityOutcome : FormulationOutcome

data FormulationExperimentCandidate : Set where
  matchedAtomisedVsContextual : FormulationExperimentCandidate
  unmatchedContextComparison : FormulationExperimentCandidate

data FormulationCriterion : Set where
  decisionDiscriminationCriterion : FormulationCriterion
  negativeControlSpecificityCriterion : FormulationCriterion
  heldOutGeneralisationCriterion : FormulationCriterion

criterion : FormulationExperimentCandidate → FormulationCriterion
criterion matchedAtomisedVsContextual = decisionDiscriminationCriterion
criterion unmatchedContextComparison = decisionDiscriminationCriterion

-- Preference is deliberately an obligation-bearing relation rather than a
-- numeric truth score.  A downstream experiment designer must establish the
-- declared matching/control conditions before claiming one design preferable.
record MatchedDesignPreference
    (preferred alternative : FormulationExperimentCandidate) : Set where
  constructor matched-design-preference
  field
    sameUnderlyingCaseMaterial : Set
    declaredSingleContrast : Set
    heldOutNegativeControl : Set
    outcomeMeasurementPlan : Set

experimentPreference :
  FormulationExperimentCandidate →
  FormulationExperimentCandidate →
  Set
experimentPreference = MatchedDesignPreference

data FormulationCriterionJustification : Set where
  consumerRelativeDecisionDiscrimination : FormulationCriterionJustification

robustExperimentDesign :
  Robust.ExperimentDesign FormulationExperimentCandidate FormulationCriterion
robustExperimentDesign =
  Robust.experimentDesign
    criterion
    experimentPreference
    FormulationCriterionJustification

------------------------------------------------------------------------
-- Concrete first-study specification.
------------------------------------------------------------------------

record FormulationExperimentSpec : Set where
  constructor formulation-experiment-spec
  field
    sameCaseMaterial : Bool
    structuralContextIsDeclaredContrast : Bool
    structuralContextIndependentlyEvidenced : Bool
    randomAssignmentPlanned : Bool
    preregisteredOutcomes : Bool
    heldOutStructuralIrrelevanceControl : Bool
    clinicianAndParticipantOutcomesSeparated : Bool
    representedActionAndActualBehaviourSeparated : Bool
    uncertaintyModelRequired : Bool
    heldOutDiscriminationRequired : Bool
    affectedConstituencyInputRequired : Bool
    attributionRulesRetained : Bool
    experimentEstablishesCounterinsurgency : Bool
    experimentEstablishesInstitutionalIntent : Bool
    onePositiveStudyEstablishesUniversalClinicalSuperiority : Bool
    acquisitionPriorityCreatesTruth : Bool

open FormulationExperimentSpec public

canonicalFormulationExperiment : FormulationExperimentSpec
canonicalFormulationExperiment =
  formulation-experiment-spec
    true   -- same case material across arms
    true   -- structural-context disclosure is the declared treatment contrast
    true   -- only independently sourced structural facts may be inserted
    true   -- random assignment is the preferred first causal design
    true   -- attribution/action/referral/confidence outcomes declared in advance
    true   -- cases where the structural coordinate is genuinely irrelevant
    true   -- clinician decisions and participant responses are distinct consumers
    true   -- perceived/represented options != enacted behaviour
    true   -- correlated uncertainty/model discrepancy remain explicit
    true   -- training/pilot fit is not scientific support
    true   -- affected constituency articulation is not replaceable by proxy labels
    true   -- source/theory/reconstruction/empirical roles remain segregated
    false  -- this study cannot by itself establish "therapy = counterinsurgency"
    false  -- effect/decision shift does not establish institutional intent
    false  -- one study does not establish universal superiority
    false  -- acquisition priority is not truth

------------------------------------------------------------------------
-- Consumer target: reuse the existing Clinic intersectional collision rather
-- than constructing another non-factorability theorem.
------------------------------------------------------------------------

atomisingStructuralCollisionReused : Bool
atomisingStructuralCollisionReused =
  Intersectionality.reusesIntersectionalNonFactorability

requiredAxisRepairReused : Bool
requiredAxisRepairReused =
  Intersectionality.reusesRequiredAxisJoin

actionSelectionConsumerReference : String
actionSelectionConsumerReference =
  "declared clinical action-selection consumer: treatment/referral/material-support/represented-action decision under matched case information"

primaryExperimentQuestion : String
primaryExperimentQuestion =
  "holding underlying case material fixed, does adding independently evidenced structural context change a declared formulation-dependent decision or action consumer, and does that difference disappear on held-out cases where the structural coordinate is irrelevant?"

------------------------------------------------------------------------
-- Investigation/acquisition Pareto: planning coordinates only.
--
-- Numeric coordinates below are explicit workflow heuristics for routing the
-- next acquisition, not evidence grades, effect sizes, probabilities, or truth.
------------------------------------------------------------------------

pinPrimarySheehiPassages : INV.InvestigationCandidate
pinPrimarySheehiPassages = INV.investigation-candidate
  "clinic-acq:primary-sheehi-passages"
  "pin exact book passages corresponding to reel claims"
  "JSTOR/Pluto primary-book passage acquisition + exact claim review"
  "lawful public/institutional access only"
  "reel -> book claim genealogy"
  "planning-axis-v1"
  8 8 7 5 2
  true refl false refl false refl

buildFormulationEvidencePacket : INV.InvestigationCandidate
buildFormulationEvidencePacket = INV.investigation-candidate
  "clinic-acq:formulation-evidence-packet"
  "assemble claim-relative formulation/context evidence packet"
  "primary/review literature packet with design and evidence ceilings"
  "public scholarly sources"
  "CFI/SCF/social-determinants -> formulation consumer"
  "planning-axis-v1"
  7 7 7 6 3
  true refl false refl false refl

preregisterPilotExperiment : INV.InvestigationCandidate
preregisterPilotExperiment = INV.investigation-candidate
  "clinic-acq:preregister-pilot"
  "operationalise atomised-vs-contextual formulation discriminator"
  "preregister matched randomized pilot with held-out irrelevance controls"
  "ethics/recruitment/resources required"
  "formal collision -> empirical decision consumer"
  "planning-axis-v1"
  10 10 9 7 8
  true refl false refl false refl

obtainExactHumanReview : INV.InvestigationCandidate
obtainExactHumanReview = INV.investigation-candidate
  "clinic-acq:exact-human-review"
  "pay exact-item review for selected source claims"
  "HumanReviewCore exact source/candidate/consumer binding"
  "qualified reviewer and durable source manifestation required"
  "source manifestation -> reviewed claim"
  "planning-axis-v1"
  6 8 5 7 5
  true refl false refl false refl

clinicAcquisitionCandidates : List INV.InvestigationCandidate
clinicAcquisitionCandidates =
  pinPrimarySheehiPassages ∷
  buildFormulationEvidencePacket ∷
  preregisterPilotExperiment ∷
  obtainExactHumanReview ∷ []

acquisitionPriorityView : INV.DirectMixedParetoView
acquisitionPriorityView = INV.investigationParetoView

------------------------------------------------------------------------
-- SOTA-to-experiment handoff.
------------------------------------------------------------------------

sotaAtlas : SOTA.ClinicSOTABoundary
sotaAtlas = SOTA.canonicalClinicSOTABoundary

record ClinicExperimentHandoffBoundary : Set where
  constructor clinic-experiment-handoff-boundary
  field
    robustExperimentOwnerReused : Bool
    acquisitionParetoOwnerReused : Bool
    existingIntersectionalityOwnerReused : Bool
    structuralDeterminantLiteratureCreatesCaseSpecificExposure : Bool
    formulationReviewCreatesOutcomeEffect : Bool
    experimentDesignCreatesEmpiricalResult : Bool
    heldOutControlRequired : Bool
    actualBehaviourRequiresSeparateMeasurement : Bool
    acquisitionPriorityCreatesSourceTruth : Bool
    experimentCanTestDecisionConsequenceWithoutTestingIntent : Bool

open ClinicExperimentHandoffBoundary public

canonicalClinicExperimentHandoffBoundary : ClinicExperimentHandoffBoundary
canonicalClinicExperimentHandoffBoundary =
  clinic-experiment-handoff-boundary
    true true true
    false false false
    true true false true

------------------------------------------------------------------------
-- Non-promotion propositions.
------------------------------------------------------------------------

data DecisionShiftProvesCounterinsurgency : Set where
data DecisionShiftProvesIntent : Set where
data FormulationReviewProvesOutcomeBenefit : Set where
data AcquisitionPriorityProvesTruth : Set where

decisionShiftDoesNotProveCounterinsurgency :
  DecisionShiftProvesCounterinsurgency → ⊥
decisionShiftDoesNotProveCounterinsurgency ()

decisionShiftDoesNotProveIntent : DecisionShiftProvesIntent → ⊥
decisionShiftDoesNotProveIntent ()

formulationReviewDoesNotProveOutcomeBenefit :
  FormulationReviewProvesOutcomeBenefit → ⊥
formulationReviewDoesNotProveOutcomeBenefit ()

acquisitionPriorityDoesNotProveTruth : AcquisitionPriorityProvesTruth → ⊥
acquisitionPriorityDoesNotProveTruth ()
