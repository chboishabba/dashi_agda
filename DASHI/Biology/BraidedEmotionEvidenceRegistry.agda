module DASHI.Biology.BraidedEmotionEvidenceRegistry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BraidedEmotionProcessBoundary as Emotion
import DASHI.Biology.BraidedEmotionTheoryContention as Contention

data EvidenceStatus : Set where
  replicatedAssociation : EvidenceStatus
  contestedAssociation : EvidenceStatus
  mechanisticCandidate : EvidenceStatus
  proxyOnly : EvidenceStatus
  theoryDependentInterpretation : EvidenceStatus
  phenomenologicalReport : EvidenceStatus
  culturalRelationalWarrant : EvidenceStatus
  normativeCommitment : EvidenceStatus

record EmotionEvidenceRow : Set where
  constructor mkEmotionEvidenceRow
  field
    claimLabel : String
    theory : Emotion.EmotionTheory
    scale : Contention.ExplanationScale
    status : EvidenceStatus
    populationOrContext : String
    supportingObservation : String
    potentialFalsifier : String
    theoremAuthorityClaimed : Bool
    clinicalAuthorityClaimed : Bool

open EmotionEvidenceRow public

record EmotionEvidenceBoundary : Set where
  constructor mkEmotionEvidenceBoundary
  field
    rows : List EmotionEvidenceRow
    technicalVocabularyIsNotEvidence : Bool
    proxyIsNotMechanism : Bool
    associationIsNotCausation : Bool
    normativeCommitmentIsNotEmpiricalResult : Bool
    emptyRegistryDoesNotPromoteTheory : Bool
    boundaryHolds : Bool
    boundaryHoldsIsTrue : boundaryHolds ≡ true

open EmotionEvidenceBoundary public

crossCulturalRegularityRow : EmotionEvidenceRow
crossCulturalRegularityRow =
  mkEmotionEvidenceRow
    "cross-cultural regularity with substantial variation"
    Emotion.basicDiscreteTheory
    Contention.culturalHistoricalScale
    contestedAssociation
    "cross-cultural recognition and production tasks with method-sensitive outcomes"
    "some affective and expressive regularities recur while category boundaries and recognition rates vary by culture and task"
    "robust context-invariant category identity across open-ended methods would strengthen a universal natural-kind reading"
    false
    false

conceptAndLanguageRow : EmotionEvidenceRow
conceptAndLanguageRow =
  mkEmotionEvidenceRow
    "concept and language modulate categorisation without unconstrained creation"
    Emotion.constructionistTheory
    Contention.phenomenologicalScale
    theoryDependentInterpretation
    "adult categorisation, learning, semantic interference, and affect-labelling paradigms"
    "available concepts and words can alter attention, differentiation, memory, report, and regulation"
    "unchanged categorisation and experience under strong concept-learning and language manipulations would count against a constitutive role"
    false
    false

interoceptiveInferenceRow : EmotionEvidenceRow
interoceptiveInferenceRow =
  mkEmotionEvidenceRow
    "interoceptive prediction is a candidate mechanism rather than a settled total theory"
    Emotion.predictiveProcessingTheory
    Contention.bodilyRegulationScale
    mechanisticCandidate
    "interoception, autonomic regulation, lesion, perturbation, and computational modelling studies"
    "bodily prediction, precision, and prediction-error constructs organise a productive account of affective regulation"
    "reliable dissociation of predicted precision effects from affective inference would weaken the proposed mechanism"
    false
    false

actionReadinessRow : EmotionEvidenceRow
actionReadinessRow =
  mkEmotionEvidenceRow
    "emotion episodes reorganise action readiness but are not reducible to one motor programme"
    Emotion.actionReadinessTheory
    Contention.actionSelectionScale
    replicatedAssociation
    "appraisal, approach-avoidance, defensive behaviour, and situated action studies"
    "emotionally significant situations systematically alter preparation, attention, and available actions"
    "absence of action-preparatory change across ecologically valid emotional episodes would challenge the action-readiness account"
    false
    false

affectLabellingRow : EmotionEvidenceRow
affectLabellingRow =
  mkEmotionEvidenceRow
    "affect labelling can regulate or reshape an episode in context-dependent ways"
    Emotion.constructionistTheory
    Contention.phenomenologicalScale
    replicatedAssociation
    "affect-labelling, reappraisal, exposure, and emotional-granularity tasks"
    "putting experience into words can change attention and regulation, while effects depend on task, timing, person, and label fit"
    "uniform harm or uniform benefit independent of context would contradict the context-sensitive boundary"
    false
    false

neuralProxyRow : EmotionEvidenceRow
neuralProxyRow =
  mkEmotionEvidenceRow
    "distributed neural measurements are proxies and do not identify a complete lived episode"
    Emotion.predictiveProcessingTheory
    Contention.neuralMechanismScale
    proxyOnly
    "fMRI, EEG, lesion, connectivity, and multivariate decoding studies"
    "distributed neural patterns can covary with tasks and reports but remain measurement- and model-dependent"
    "validated person-independent recovery of episode meaning from neural data alone would challenge the present proxy boundary"
    false
    false

relationalConstitutionRow : EmotionEvidenceRow
relationalConstitutionRow =
  mkEmotionEvidenceRow
    "some emotion meanings depend on relation, institution, history, and power"
    Emotion.socialRelationalTheory
    Contention.interpersonalScale
    culturalRelationalWarrant
    "interpersonal, developmental, anthropological, institutional, and situated qualitative inquiry"
    "shame, grief, gratitude, indignation, belonging, and trust often cannot be individuated without specifying consequential relations"
    "complete preservation of episode meaning after removal of relational and historical context would weaken the constitutive claim"
    false
    false

reciprocalObligationRow : EmotionEvidenceRow
reciprocalObligationRow =
  mkEmotionEvidenceRow
    "knowing another person's state can generate obligations of care, restraint, consent, or repair"
    Emotion.socialRelationalTheory
    Contention.ethicalGovernanceScale
    normativeCommitment
    "ethical and relational governance rather than empirical mechanism testing"
    "classification is not treated as ethically neutral when naming affects agency, care, risk, and social response"
    "this is a revisable normative commitment and is not promoted as an empirical theorem"
    false
    false

canonicalEmotionEvidenceRows : List EmotionEvidenceRow
canonicalEmotionEvidenceRows =
  crossCulturalRegularityRow
  ∷ conceptAndLanguageRow
  ∷ interoceptiveInferenceRow
  ∷ actionReadinessRow
  ∷ affectLabellingRow
  ∷ neuralProxyRow
  ∷ relationalConstitutionRow
  ∷ reciprocalObligationRow
  ∷ []

canonicalEmotionEvidenceBoundary : EmotionEvidenceBoundary
canonicalEmotionEvidenceBoundary =
  mkEmotionEvidenceBoundary
    canonicalEmotionEvidenceRows
    true
    true
    true
    true
    true
    true
    refl

canonicalEvidenceRowsAreInstantiated :
  rows canonicalEmotionEvidenceBoundary ≡ canonicalEmotionEvidenceRows
canonicalEvidenceRowsAreInstantiated = refl
