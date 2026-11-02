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
import DASHI.Biology.AliceBrownDissentGovernanceCrossPollinationExact as Dissent
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as Agency
import DASHI.Culture.CohnInstitutionalFeministTwoEyedCrossPollinationExact as Cohn
import DASHI.Biology.AliceBrownDependencyDerivedInvalidationBidiExact as Invalidation
import DASHI.Core.DependencyDerivedMinimalInvalidationBidiExact as Derived
import DASHI.Biology.TraumaRelationalLearningNonpromotionExact as Trauma
import DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge as BodyMemory
import DASHI.Cognition.PNF.TrialecticMemoryLearningHyperfabricExact as Learning
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.IntersectionalBinaryInteractionBridgeExact as Interaction
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.ObserverRefinementLatticeExact as Observer
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
    intersectionalJointInteraction : Interaction.IntersectionalInteractionAdmission
    bodyMemoryHyperfabric : BodyMemory.HyperfabricIntersectionalBodyMemoryBridge
    bodyMemoryIsCanonical :
      bodyMemoryHyperfabric ≡ BodyMemory.canonicalHyperfabricIntersectionalBodyMemoryBridge
    bodyMemorySourceCertificate :
      BodyMemory.HyperfabricIntersectionalBodyMemoryCertificate bodyMemoryHyperfabric
    positiveFeministRepair :
      Feminist.PositiveRecharting {Residual = Feminist.PositiveMultiplicity} Feminist.inheritedChart
    strictFeministRechart :
      Observer.StrictRefinement
        Feminist.inheritedChart
        (Observer.pairObserver
          Feminist.inheritedChart
          (Feminist.PositiveRecharting.residual positiveFeministRepair))
    categoricalMethod : McCall.CategoryStrategy
    sourceVoiceGate : Voice.StudentVoiceEpistemicAgencyBridge
    parentMultiObserver : MultiObserver.ParentAllyshipMultiObserverBridge
    traumaNonpromotion : Trauma.TraumaRelationalLearningBoundary
    trialecticLearning : Learning.TrialecticMemoryLearningBoundary
    aliceTemporalDiagnosis : TimeLineage.AliceBrownTemporalDiagnosisBoundary
    aliceDissentGovernance : Dissent.AliceBrownDissentGovernanceBoundary
    institutionalAgencyBoundary : Agency.AliceInstitutionalChoiceBoundary
    attributedFeministTwoEyedBoundary : Cohn.CrossPollinationBoundary

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
    Interaction.canonicalIntersectionalInteractionAdmission
    BodyMemory.canonicalHyperfabricIntersectionalBodyMemoryBridge refl
    BodyMemory.canonicalHyperfabricIntersectionalBodyMemoryCertificate
    Feminist.canonicalPositiveRecharting
    (Feminist.positiveRechartingStrictlyRefinesInheritedChart
      Feminist.canonicalPositiveRecharting)
    McCall.intercategorical
    Voice.canonicalStudentVoiceEpistemicAgencyBridge
    MultiObserver.canonicalParentAllyshipMultiObserverBridge
    Trauma.canonicalTraumaRelationalLearningBoundary
    Learning.canonicalTrialecticMemoryLearningBoundary
    TimeLineage.canonicalAliceBrownTemporalDiagnosisBoundary
    Dissent.canonicalAliceBrownDissentGovernanceBoundary
    Agency.canonicalAliceInstitutionalChoiceBoundary
    Cohn.canonicalCrossPollinationBoundary
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
  Derived.DerivedInvalidatedAxis
    Invalidation.aliceInvalidationProblem
aliceDerivedDependencyOwner = Invalidation.aliceDerivedDiagnosticInvalidation
