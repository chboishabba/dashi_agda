module DASHI.Biology.AutismVaccinePersuasionMediaExtensionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.AutismVaccineClaimPromotionAuditExact as Audit

------------------------------------------------------------------------
-- PERSUASION / MISINFORMATION EXTENSION
--
-- The attached transcript cites Nyhan et al. while asking how minds change.
-- This module preserves the specific vaccine-message trial separately from the
-- broader, later literature on correction effectiveness.  A study-specific
-- counterproductive response does not become a universal "fact checking makes
-- people believe misinformation more" law.
------------------------------------------------------------------------

data CommunicationEvidenceKind : Set where
  randomizedSurveyExperiment : CommunicationEvidenceKind
  replicationStudy : CommunicationEvidenceKind
  systematicReview : CommunicationEvidenceKind
  reviewConsensus : CommunicationEvidenceKind

data CommunicationOutcome : Set where
  factualBeliefAccuracy : CommunicationOutcome
  vaccineMisperception : CommunicationOutcome
  vaccinationIntent : CommunicationOutcome
  vaccinationBehaviour : CommunicationOutcome
  sourceTrust : CommunicationOutcome
  salience : CommunicationOutcome

data CommunicationDirection : Set where
  improves : CommunicationDirection
  worsens : CommunicationDirection
  noDetectableChange : CommunicationDirection
  mixedOrSubgroupDependent : CommunicationDirection

record CommunicationEvidenceReceipt : Set where
  constructor communication-evidence-receipt
  field
    sourceKey : String
    evidenceKind : CommunicationEvidenceKind
    targetOutcome : CommunicationOutcome
    direction : CommunicationDirection
    paidReading : String
    scopeBoundary : String

open CommunicationEvidenceReceipt public

nyhan2014MMRTrial : CommunicationEvidenceReceipt
nyhan2014MMRTrial =
  communication-evidence-receipt
    "nyhan-reifler-richey-freed-2014-mmr-messaging"
    randomizedSurveyExperiment
    vaccinationIntent
    mixedOrSubgroupDependent
    "A nationally representative US survey experiment of 1,759 parents tested several MMR-promotion messages; interventions did not increase parental intent to vaccinate overall, and some messages produced counterproductive responses on selected outcomes/subgroups."
    "This pays the trial-specific message/outcome result. It does not establish that corrections universally backfire, that all misinformation correction is futile, or that belief accuracy and vaccination intent are the same endpoint."

laterBackfireReplicationBoundary : CommunicationEvidenceReceipt
laterBackfireReplicationBoundary =
  communication-evidence-receipt
    "later-correction-backfire-replication-boundary"
    replicationStudy
    factualBeliefAccuracy
    improves
    "Later misinformation-correction studies generally find that corrections improve belief accuracy and often fail to reproduce a general backfire effect."
    "Backfire can remain context-dependent, including source distrust/scepticism; this receipt blocks a universal no-backfire theorem as well as a universal backfire theorem."

communicationReviewBoundary : CommunicationEvidenceReceipt
communicationReviewBoundary =
  communication-evidence-receipt
    "correction-effectiveness-review-boundary"
    reviewConsensus
    factualBeliefAccuracy
    improves
    "Review-level evidence supports corrections as usually at least somewhat effective for accuracy, while durability and behavioural transfer may be weaker than immediate belief correction."
    "Accuracy, persistence, intent and behaviour remain distinct outcomes; elite/media cues and source trust can moderate effects."

canonicalCommunicationReceipts : List CommunicationEvidenceReceipt
canonicalCommunicationReceipts =
  nyhan2014MMRTrial ∷ laterBackfireReplicationBoundary ∷
  communicationReviewBoundary ∷ []

------------------------------------------------------------------------
-- OUTCOME NON-COLLAPSE.
------------------------------------------------------------------------

data AccurateBeliefAutomaticallyCreatesVaccinationPermission : Set where
data TrialCounterproductiveResponseCreatesUniversalBackfirePermission : Set where
data MediaExposureAutomaticallyCreatesBeliefPermission : Set where
data BeliefAutomaticallyCreatesBehaviourPermission : Set where

accuracyDoesNotDefinitionallyCreateVaccination :
  AccurateBeliefAutomaticallyCreatesVaccinationPermission → ⊥
accuracyDoesNotDefinitionallyCreateVaccination ()

trialBackfireDoesNotCreateUniversalBackfire :
  TrialCounterproductiveResponseCreatesUniversalBackfirePermission → ⊥
trialBackfireDoesNotCreateUniversalBackfire ()

mediaExposureDoesNotDefinitionallyCreateBelief :
  MediaExposureAutomaticallyCreatesBeliefPermission → ⊥
mediaExposureDoesNotDefinitionallyCreateBelief ()

beliefDoesNotDefinitionallyCreateBehaviour :
  BeliefAutomaticallyCreatesBehaviourPermission → ⊥
beliefDoesNotDefinitionallyCreateBehaviour ()

------------------------------------------------------------------------
-- PROPAGATION CHAIN.
--
-- Media amplification can be studied as a causal chain, but every transition
-- must have its own receipt.  This separates content truth from source reach,
-- repeated salience, belief update, intention and eventual behaviour.
------------------------------------------------------------------------

data PropagationStage : Set where
  propositionContent : PropagationStage
  sourcePublication : PropagationStage
  mediaAmplification : PropagationStage
  audienceExposure : PropagationStage
  salienceOrAvailability : PropagationStage
  beliefState : PropagationStage
  behaviouralIntent : PropagationStage
  observedBehaviour : PropagationStage
  populationHealthOutcome : PropagationStage

record PropagationEdgeRequirement : Set where
  constructor propagation-edge-requirement
  field
    fromStage : PropagationStage
    toStage : PropagationStage
    edgeReference : String
    automatic : Bool
    automaticIsFalse : automatic ≡ false

open PropagationEdgeRequirement public

publicationToAmplification : PropagationEdgeRequirement
publicationToAmplification =
  propagation-edge-requirement sourcePublication mediaAmplification
    "Publication alone does not determine media uptake; amplification depends on newsroom, authority, novelty, conflict and other selection mechanisms."
    false refl

amplificationToExposure : PropagationEdgeRequirement
amplificationToExposure =
  propagation-edge-requirement mediaAmplification audienceExposure
    "Broadcast volume does not establish individual exposure without audience/reach measurement."
    false refl

exposureToBelief : PropagationEdgeRequirement
exposureToBelief =
  propagation-edge-requirement audienceExposure beliefState
    "Exposure can affect belief under some designs but does not automatically set belief state."
    false refl

beliefToIntent : PropagationEdgeRequirement
beliefToIntent =
  propagation-edge-requirement beliefState behaviouralIntent
    "Belief accuracy and vaccination intention are empirically distinct endpoints."
    false refl

intentToBehaviour : PropagationEdgeRequirement
intentToBehaviour =
  propagation-edge-requirement behaviouralIntent observedBehaviour
    "Intention does not definitionally equal observed uptake."
    false refl

behaviourToPopulationOutcome : PropagationEdgeRequirement
behaviourToPopulationOutcome =
  propagation-edge-requirement observedBehaviour populationHealthOutcome
    "Population health effects require coverage, transmission, susceptibility and epidemiologic context rather than individual behaviour alone."
    false refl

canonicalPropagationRequirements : List PropagationEdgeRequirement
canonicalPropagationRequirements =
  publicationToAmplification ∷ amplificationToExposure ∷ exposureToBelief ∷
  beliefToIntent ∷ intentToBehaviour ∷ behaviourToPopulationOutcome ∷ []

------------------------------------------------------------------------
-- CROSS-POLLINATION WITH THE MAIN AUDIT.
------------------------------------------------------------------------

record PersuasionCrossPollination : Set where
  constructor persuasion-cross-pollination
  field
    mainAuditReference : String
    cognitiveWarfareReference : String
    traumaMemoryDecisionReference : String
    sourceProvenanceReference : String
    observerReference : String
    reading : String

canonicalPersuasionCrossPollination : PersuasionCrossPollination
canonicalPersuasionCrossPollination =
  persuasion-cross-pollination
    "DASHI.Biology.AutismVaccineClaimPromotionAuditExact"
    "existing cognitive-warfare/FIMI detection formalism: propagation structure and provenance are measurable without inferring content truth from coordination or reach"
    "existing trauma-memory-learning-decision formalism: salience, recall, temporal ordering and decision state remain separate from causal truth"
    "DASHI.Core.AttributedSourceCore"
    "existing multi-observer / participant-voice machinery"
    "The Hbomberguy media narrative is represented as a candidate propagation chain. Each content -> publication -> amplification -> exposure -> belief -> intent -> behaviour -> population-outcome edge requires its own empirical receipt."

record PersuasionMediaBoundary : Set where
  constructor persuasion-media-boundary
  field
    nyhanTrialRepresented : Bool
    nyhanTrialRepresentedIsTrue : nyhanTrialRepresented ≡ true
    universalBackfireLawPaid : Bool
    universalBackfireLawPaidIsFalse : universalBackfireLawPaid ≡ false
    correctionUsuallyImprovesAccuracyRepresented : Bool
    correctionUsuallyImprovesAccuracyRepresentedIsTrue : correctionUsuallyImprovesAccuracyRepresented ≡ true
    accuracyCollapsedWithIntent : Bool
    accuracyCollapsedWithIntentIsFalse : accuracyCollapsedWithIntent ≡ false
    intentCollapsedWithBehaviour : Bool
    intentCollapsedWithBehaviourIsFalse : intentCollapsedWithBehaviour ≡ false
    mediaNarrativePromotedToCausalLaw : Bool
    mediaNarrativePromotedToCausalLawIsFalse : mediaNarrativePromotedToCausalLaw ≡ false
    propositionTruthSeparatedFromPropagation : Bool
    propositionTruthSeparatedFromPropagationIsTrue : propositionTruthSeparatedFromPropagation ≡ true

open PersuasionMediaBoundary public

canonicalPersuasionMediaBoundary : PersuasionMediaBoundary
canonicalPersuasionMediaBoundary =
  persuasion-media-boundary
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl
