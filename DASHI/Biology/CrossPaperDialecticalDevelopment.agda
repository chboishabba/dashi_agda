module DASHI.Biology.CrossPaperDialecticalDevelopment where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources

------------------------------------------------------------------------
-- Cross-paper developmental relation.
--
-- A source paper, a cross-paper inference and a DASHI extension remain
-- distinct claim registers.  The sequence below is a corpus-level synthesis,
-- not a claim that any one paper states the entire programme.

data ClaimRegister : Set where
  sourcePaperClaim : ClaimRegister
  crossPaperInference : ClaimRegister
  dashiFormalExtension : ClaimRegister
  empiricalFollowUpHypothesis : ClaimRegister


data DevelopmentStage : Set where
  engagementFibreStage : DevelopmentStage
  scalableFeedbackClassificationStage : DevelopmentStage
  teacherDesignedHumourFrameworkStage : DevelopmentStage
  ecologicalContextRestorationStage : DevelopmentStage
  epistemicAgencyRedistributionStage : DevelopmentStage
  studentIdentifiedSupportStage : DevelopmentStage
  multiObserverAllyshipStage : DevelopmentStage
  coDesignedEnactmentStage : DevelopmentStage
  evidenceReturnRechartingStage : DevelopmentStage

canonicalDevelopmentStages : List DevelopmentStage
canonicalDevelopmentStages =
  engagementFibreStage
  ∷ scalableFeedbackClassificationStage
  ∷ teacherDesignedHumourFrameworkStage
  ∷ ecologicalContextRestorationStage
  ∷ epistemicAgencyRedistributionStage
  ∷ studentIdentifiedSupportStage
  ∷ multiObserverAllyshipStage
  ∷ coDesignedEnactmentStage
  ∷ evidenceReturnRechartingStage
  ∷ []

stageName : DevelopmentStage → String
stageName engagementFibreStage = "name overlapping engagement fibres"
stageName scalableFeedbackClassificationStage = "scale feedback classification"
stageName teacherDesignedHumourFrameworkStage =
  "construct teacher-designed seven-consideration humour framework"
stageName ecologicalContextRestorationStage = "restore person-place ecology"
stageName epistemicAgencyRedistributionStage = "redistribute epistemic agency"
stageName studentIdentifiedSupportStage = "route student-identified support candidates"
stageName multiObserverAllyshipStage = "preserve plural observer and allyship fibres"
stageName coDesignedEnactmentStage = "co-design local enactment"
stageName evidenceReturnRechartingStage = "return evidence and revise the chart"

data CrossPaperRelationKind : Set where
  suppliesVocabulary : CrossPaperRelationKind
  scalesInterpretation : CrossPaperRelationKind
  correctsExtractiveRisk : CrossPaperRelationKind
  restoresEcologicalContext : CrossPaperRelationKind
  suppliesCandidateHandles : CrossPaperRelationKind
  addsObserverFibre : CrossPaperRelationKind
  suppliesGovernanceGate : CrossPaperRelationKind
  exposesProjectionBoundary : CrossPaperRelationKind
  proposesEmpiricalFollowUp : CrossPaperRelationKind

record CrossPaperRelation : Set where
  constructor mkCrossPaperRelation
  field
    relationLabel : String
    sourcePaper : Sources.PaperReference
    targetPaper : Sources.PaperReference
    relationKind : CrossPaperRelationKind
    claimRegister : ClaimRegister
    preservedContribution : String
    nonPromotionBoundary : String
    relationSourceBound : Bool
    relationSourceBoundIsTrue : relationSourceBound ≡ true

open CrossPaperRelation public

aiToVoiceRelation : CrossPaperRelation
aiToVoiceRelation =
  mkCrossPaperRelation
    "feedback classification to epistemic participation"
    Sources.aiFeedbackPaper
    Sources.voiceAgencyPaper
    correctsExtractiveRisk
    crossPaperInference
    "The later voice/agency critique can govern the earlier feedback-classification pipeline by requiring student participation beyond passive data provision."
    "The relation is a corpus synthesis; it does not imply that the 2024 paper was invalid or that the 2026 paper empirically tests the classifier."
    true refl

humourToVoiceRelation : CrossPaperRelation
humourToVoiceRelation =
  mkCrossPaperRelation
    "teacher-designed humour framework to constitutive epistemic agency"
    Sources.humourFrameworkPaper
    Sources.voiceAgencyPaper
    correctsExtractiveRisk
    crossPaperInference
    "The seven humour considerations are preserved as a useful teacher-side pedagogical projection while the later Brown/Kimber distinction asks which inquiry decisions students may shape before they are reduced to audience or feedback roles."
    "The later paper does not invalidate the humour framework or empirically test it; the governance relation is a DASHI cross-paper synthesis."
    true refl

humourToEcologyRelation : CrossPaperRelation
humourToEcologyRelation =
  mkCrossPaperRelation
    "audience/context descriptor to situated person-place ecology"
    Sources.humourFrameworkPaper
    Sources.ecologyOfDataPaper
    restoresEcologicalContext
    crossPaperInference
    "Audience/context can be recharted from a flat demographic descriptor into a relational person-place surface carrying teacher, peer, institutional, life-context and intersectional relations."
    "The ecology paper does not claim a humour-specific causal model, and omitted context cannot be reconstructed from feedback alone."
    true refl

aiToEcologyRelation : CrossPaperRelation
aiToEcologyRelation =
  mkCrossPaperRelation
    "feedback surface to ecology of data"
    Sources.aiFeedbackPaper
    Sources.ecologyOfDataPaper
    restoresEcologicalContext
    crossPaperInference
    "The ecology-of-data stance restores person-place transactions, affordances, minutiae and value flows hidden by flat aggregate coding."
    "The relation does not claim hidden context can be reconstructed from the comment alone."
    true refl

aiToSupportRelation : CrossPaperRelation
aiToSupportRelation =
  mkCrossPaperRelation
    "OEF residuals to student-identified support families"
    Sources.aiFeedbackPaper
    Sources.onlineSupportStrategiesPaper
    suppliesCandidateHandles
    empiricalFollowUpHypothesis
    "OEF residual signals may be cross-tested against five student-identified support families as optional +1 candidates."
    "No fixed category-to-intervention causal table is established by the two papers."
    true refl

voiceToSupportRelation : CrossPaperRelation
voiceToSupportRelation =
  mkCrossPaperRelation
    "student voice to support choice"
    Sources.voiceAgencyPaper
    Sources.onlineSupportStrategiesPaper
    suppliesGovernanceGate
    crossPaperInference
    "Student-identified strategies become stronger when students may shape, choose, reject and review the proposed support."
    "Student identification in one study does not make a strategy universally preferred."
    true refl

allyshipToPartnershipRelation : CrossPaperRelation
allyshipToPartnershipRelation =
  mkCrossPaperRelation
    "parental allyship to partnership barriers"
    Sources.parentalAllyshipLensPaper
    Sources.partnershipBarriersPaper
    addsObserverFibre
    crossPaperInference
    "The conceptual lens and empirical barrier study jointly motivate a parent-ally observer fibre carrying expertise and disability-adjacent experience."
    "Parent testimony remains distinct from child voice and does not alone prove institutional intent."
    true refl

advocacyToLensRelation : CrossPaperRelation
advocacyToLensRelation =
  mkCrossPaperRelation
    "advocacy/allyship distinction to conceptual proximity lens"
    Sources.advocacyAllyshipPaper
    Sources.parentalAllyshipLensPaper
    suppliesVocabulary
    crossPaperInference
    "The empirical distinction between advocacy and allyship supports a vocabulary of primary, vicarious and primary-adjacent experience."
    "The qualitative sources do not establish prevalence or universal parent trajectories."
    true refl

canonicalCrossPaperRelations : List CrossPaperRelation
canonicalCrossPaperRelations =
  aiToVoiceRelation
  ∷ humourToVoiceRelation
  ∷ humourToEcologyRelation
  ∷ aiToEcologyRelation
  ∷ aiToSupportRelation
  ∷ voiceToSupportRelation
  ∷ allyshipToPartnershipRelation
  ∷ advocacyToLensRelation
  ∷ []

record CrossPaperDialecticalDevelopment : Set where
  constructor mkCrossPaperDialecticalDevelopment
  field
    registry : Sources.EducationCorpusSourceRegistry
    registryIsCanonical : registry ≡ Sources.canonicalEducationCorpusSourceRegistry
    stages : List DevelopmentStage
    stagesAreCanonical : stages ≡ canonicalDevelopmentStages
    relations : List CrossPaperRelation
    relationsAreCanonical : relations ≡ canonicalCrossPaperRelations
    sourceInferenceExtensionSeparated : Bool
    sourceInferenceExtensionSeparatedIsTrue :
      sourceInferenceExtensionSeparated ≡ true
    laterPaperMayCorrectWithoutErasingEarlierContribution : Bool
    laterPaperMayCorrectWithoutErasingEarlierContributionIsTrue :
      laterPaperMayCorrectWithoutErasingEarlierContribution ≡ true
    crossPaperRelationsRemainCandidates : Bool
    crossPaperRelationsRemainCandidatesIsTrue :
      crossPaperRelationsRemainCandidates ≡ true
    empiricalCrossTestingRequired : Bool
    empiricalCrossTestingRequiredIsTrue : empiricalCrossTestingRequired ≡ true
    reading : String

open CrossPaperDialecticalDevelopment public

canonicalCrossPaperDialecticalDevelopment : CrossPaperDialecticalDevelopment
canonicalCrossPaperDialecticalDevelopment =
  mkCrossPaperDialecticalDevelopment
    Sources.canonicalEducationCorpusSourceRegistry refl
    canonicalDevelopmentStages refl
    canonicalCrossPaperRelations refl
    true refl
    true refl
    true refl
    true refl
    "The corpus is represented as a developmental braid: engagement vocabulary, scalable classification, a teacher-designed humour framework, ecological restoration, epistemic participation, student-identified support, multi-observer allyship, co-designed enactment and evidence-return recharting. The humour framework is sublated rather than erased: its seven practical considerations remain useful while later papers expose the governance, observer and contextual distinctions suppressed by a teacher-side projection. This ordering is a DASHI cross-paper synthesis and remains open to empirical testing."
