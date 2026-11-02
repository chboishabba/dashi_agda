module DASHI.Education.DigitalESDCrossCorpusIntersectionalMemoryLensExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.EducationCorpusSourceRegistry as AliceSource
import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.ParentAllyshipMultiObserverBridge as MultiObserver
import DASHI.Biology.AliceBrownTemporalDiagnosisDependencyLineageBidiExact as TimeLineage
import DASHI.Biology.AliceBrownDependencyDerivedInvalidationBidiExact as Invalidation
import DASHI.Biology.TraumaRelationalLearningNonpromotionExact as Trauma
import DASHI.Cognition.PNF.TrialecticMemoryLearningHyperfabricExact as Learning
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.McCallCategoryStrategyBoundaryExact as McCall
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as EfS
import DASHI.Education.DigitalESDJointHyperfabricConsumerExact as Joint

------------------------------------------------------------------------
-- Cross-corpus application of EXISTING owners, not a new source ontology.
-- A feminist/Crenshaw/McCall/trauma/learning theorem is not automatically
-- an empirical result of Alice, an EfS paper, or a diagnosis of participants.
-- The reviewed source hyperedge belongs to JointReviewHyperedge, separately.
------------------------------------------------------------------------

record CandidateCrossCorpusLens
    (alicePaper : AliceSource.PaperReference)
    (efsCase : EfS.CrossPollinationCase) : Set₁ where
  constructor candidate-cross-corpus-lens
  field
    aliceSource : AliceSource.PaperReference
    aliceSourceIsExact : aliceSource ≡ alicePaper
    efsSourceCase : EfS.CrossPollinationCase
    efsCaseIsExact : efsSourceCase ≡ efsCase

    aliceLoom : Alice.AliceBrownCorpusLoom
    aliceLoomIsCanonical : aliceLoom ≡ Alice.canonicalAliceBrownCorpusLoom
    candidate : Joint.CandidateJointHyperedge efsSourceCase

    -- Own the actual existing *mathematical* boundaries: no re-authoring.
    intersectionalCollision :
      Intersection.NonFactorabilityWitness
        Intersection.flatProjection Intersection.relationalOutcome
    positiveFeministRepair :
      Feminist.PositiveRecharting Feminist.inheritedChart
    categoricalMethod : McCall.CategoryStrategy
    traumaNonpromotion : Trauma.TraumaRelationalLearningBoundary
    trialecticLearning : Learning.TrialecticMemoryLearningBoundary
    aliceTemporalDiagnosis : TimeLineage.AliceBrownTemporalDiagnosisBoundary

    researcherQuestion : String
    missingSourceSpecificEvidence : String
    interpretiveCandidateOnly : Bool
    interpretiveCandidateOnlyIsTrue : interpretiveCandidateOnly ≡ true

open CandidateCrossCorpusLens public

candidateLens :
  (alicePaper : AliceSource.PaperReference) →
  (efsCase : EfS.CrossPollinationCase) →
  String → String →
  CandidateCrossCorpusLens alicePaper efsCase
candidateLens alicePaper efsCase question debt =
  candidate-cross-corpus-lens
    alicePaper refl
    efsCase refl
    Alice.canonicalAliceBrownCorpusLoom refl
    (Joint.candidateJointHyperedge efsCase)
    Intersection.canonicalIntersectionalNonFactorability
    Feminist.canonicalPositiveRecharting
    McCall.intercategorical
    Trauma.canonicalTraumaRelationalLearningBoundary
    Learning.canonicalTrialecticMemoryLearningBoundary
    TimeLineage.canonicalAliceBrownTemporalDiagnosisBoundary
    question debt true refl

-- Five explicitly attributed, candidate-only questions covering distinct
-- original paper fibres; they do not assert that either author group made
-- these cross-source claims, or that their empirical units can be transported.

voiceCollectiveAuthority :
  CandidateCrossCorpusLens AliceSource.voiceAgencyPaper EfS.adefilaEcoCOIL
voiceCollectiveAuthority =
  candidateLens AliceSource.voiceAgencyPaper EfS.adefilaEcoCOIL
    "Does student co-design entail consequential community decision power?"
    "Inspect both source passages, actor roles, collective veto/decision rights, context transfer and actual outcomes. Student consultation cannot speak for communities."

allyshipCommunityAuthority :
  CandidateCrossCorpusLens AliceSource.parentalAllyshipLensPaper EfS.singhCommunity
allyshipCommunityAuthority =
  candidateLens AliceSource.parentalAllyshipLensPaper EfS.singhCommunity
    "When do situated parent/learner observers and university/community partners exercise distinct authority?"
    "Do not equate child, parent, researcher, institution and community observers. Obtain source- and participant-specific governance receipts before transfer."

dataEcologyMoreThanHuman :
  CandidateCrossCorpusLens AliceSource.ecologyOfDataPaper EfS.blackRyanJiNature
dataEcologyMoreThanHuman =
  candidateLens AliceSource.ecologyOfDataPaper EfS.blackRyanJiNature
    "Can feedback custodianship represent ecological/more-than-human relationships?"
    "Ecological relationships may require wholly new observations, concepts and governance. Human feedback recharting alone cannot recover erased ecological distinctions."

aiFeedbackEffectiveAccess :
  CandidateCrossCorpusLens AliceSource.aiFeedbackPaper EfS.jepsenCookeAccessibility
aiFeedbackEffectiveAccess =
  candidateLens AliceSource.aiFeedbackPaper EfS.jepsenCookeAccessibility
    "Do engagement classifier categories preserve disability-specific effective access?"
    "Require precise accessibility contexts, participant voice and nonfactorability tests. Classifier feasibility cannot become disabled learners' meaning or access."

studentSupportSustainableTransformation :
  CandidateCrossCorpusLens AliceSource.onlineSupportStrategiesPaper EfS.taimurOnuki
studentSupportSustainableTransformation =
  candidateLens AliceSource.onlineSupportStrategiesPaper EfS.taimurOnuki
    "Which student-chosen support arrangements endure or enable sustainability inquiry in situated course designs?"
    "Teacher-education survey preferences and two university course cases are distinct methods, contexts and populations. Learning, transformation, durability and ecological effect remain separately unmeasured."

-- Source-specific source/claim/observation review cannot be manufactured by a
-- canonical *structural* donor or a candidate interpretation.
data FeministRechartingCreatesReviewedSourceSpan : Set where
data MemoryLearningBoundaryProvesStudentOutcome : Set where
data TraumaAdaptationProvesBeneficialExposure : Set where
data CommonIntersectionalAxisAuthorisesCrossPopulationTransport : Set where
data CandidateCrossCorpusLensImpliesReviewedHyperedge : Set where
data StudentVoiceAutomaticallyGrantsCommunityAuthority : Set where

rechartingNotSourceReview :
  FeministRechartingCreatesReviewedSourceSpan → ⊥
rechartingNotSourceReview ()

memoryBoundaryNotOutcome :
  MemoryLearningBoundaryProvesStudentOutcome → ⊥
memoryBoundaryNotOutcome ()

adaptationNotBenefit :
  TraumaAdaptationProvesBeneficialExposure → ⊥
adaptationNotBenefit ()

intersectionalLabelsNotPopulationTransport :
  CommonIntersectionalAxisAuthorisesCrossPopulationTransport → ⊥
intersectionalLabelsNotPopulationTransport ()

candidateLensNotReviewed :
  CandidateCrossCorpusLensImpliesReviewedHyperedge → ⊥
candidateLensNotReviewed ()

studentVoiceNotCommunityAuthority :
  StudentVoiceAutomaticallyGrantsCommunityAuthority → ⊥
studentVoiceNotCommunityAuthority ()

-- Retain the existing Alice selective-revision owner separately. This is
-- one real dependency-derived example, not a source-reviewed EfS revision.
aliceDerivedDependencyOwner :
  Invalidation.Derived.DerivedInvalidatedAxis
    Invalidation.aliceInvalidationProblem
aliceDerivedDependencyOwner = Invalidation.aliceDerivedDiagnosticInvalidation
