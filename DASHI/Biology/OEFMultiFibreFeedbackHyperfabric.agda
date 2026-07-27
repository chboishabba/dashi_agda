module DASHI.Biology.OEFMultiFibreFeedbackHyperfabric where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Source-bound OEF / AI feedback formalisation.
--
-- Primary source:
--   Dann, Christopher; Redmond, Petrea; Fanshawe, Melissa; Brown, Alice;
--   Getenet, Seyum; Shaik, Thanveer; Tao, Xiaohui; Galligan, Linda; Li, Yan.
--   "Making sense of student feedback and engagement using artificial
--   intelligence." Australasian Journal of Educational Technology 40(3),
--   58-76 (2024). DOI: 10.14742/ajet.8903.
--
-- Formal position:
--   - the paper is retained as an MVP / feasibility evidence surface;
--   - the five OEF elements are overlapping fibres, not exclusive essences;
--   - human labels are compiled into a classifier rather than removed;
--   - end-of-course feedback is a sparse, self-selected, time-local
--     projection of a larger student ecology;
--   - model outputs route human attention but do not become student meaning,
--     complete voice, learning truth, equity, diagnosis, or pedagogical
--     authority.

------------------------------------------------------------------------
-- Generic helpers.

data Never : Set where

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Paper metadata.

record PaperReference : Set where
  constructor mkPaperReference
  field
    paperTitle : String
    paperAuthors : List String
    paperJournal : String
    paperYear : Nat
    paperVolume : Nat
    paperIssue : Nat
    paperPages : String
    paperDOI : String
    paperInstitution : String
    paperStudyReading : String

open PaperReference public

canonicalPaperAuthors : List String
canonicalPaperAuthors =
  "Christopher Dann"
  ∷ "Petrea Redmond"
  ∷ "Melissa Fanshawe"
  ∷ "Alice Brown"
  ∷ "Seyum Getenet"
  ∷ "Thanveer Shaik"
  ∷ "Xiaohui Tao"
  ∷ "Linda Galligan"
  ∷ "Yan Li"
  ∷ []

canonicalPaperReference : PaperReference
canonicalPaperReference =
  mkPaperReference
    "Making sense of student feedback and engagement using artificial intelligence"
    canonicalPaperAuthors
    "Australasian Journal of Educational Technology"
    2024
    40
    3
    "58-76"
    "10.14742/ajet.8903"
    "University of Southern Queensland, Toowoomba, Queensland, Australia"
    "MVP feasibility study: manually labelled OEF feedback can train a scalable classification and visualisation prototype; semantic, ecological, longitudinal, and pedagogical closure are not promoted."

canonicalPaperTitle : paperTitle canonicalPaperReference ≡ "Making sense of student feedback and engagement using artificial intelligence"
canonicalPaperTitle = refl

canonicalPaperDOI : paperDOI canonicalPaperReference ≡ "10.14742/ajet.8903"
canonicalPaperDOI = refl

canonicalPaperAuthorCount : listCount canonicalPaperAuthors ≡ 9
canonicalPaperAuthorCount = refl

------------------------------------------------------------------------
-- Five Online Engagement Framework fibres.

data OEFElement : Set where
  socialEngagement : OEFElement
  cognitiveEngagement : OEFElement
  behaviouralEngagement : OEFElement
  collaborativeEngagement : OEFElement
  emotionalEngagement : OEFElement

canonicalOEFElements : List OEFElement
canonicalOEFElements =
  socialEngagement
  ∷ cognitiveEngagement
  ∷ behaviouralEngagement
  ∷ collaborativeEngagement
  ∷ emotionalEngagement
  ∷ []

canonicalOEFElementCount : listCount canonicalOEFElements ≡ 5
canonicalOEFElementCount = refl

oefElementName : OEFElement → String
oefElementName socialEngagement = "social engagement"
oefElementName cognitiveEngagement = "cognitive engagement"
oefElementName behaviouralEngagement = "behavioural engagement"
oefElementName collaborativeEngagement = "collaborative engagement"
oefElementName emotionalEngagement = "emotional engagement"

record OEFElementProfile : Set where
  constructor mkOEFElementProfile
  field
    profileElement : OEFElement
    profileIndicators : List String
    profileInterconnected : Bool
    profileInterconnectedIsTrue : profileInterconnected ≡ true
    profileDynamic : Bool
    profileDynamicIsTrue : profileDynamic ≡ true
    profileMultidimensional : Bool
    profileMultidimensionalIsTrue : profileMultidimensional ≡ true

open OEFElementProfile public

socialProfile : OEFElementProfile
socialProfile =
  mkOEFElementProfile
    socialEngagement
    ( "building community"
    ∷ "creating a sense of belonging"
    ∷ "developing relationships"
    ∷ "establishing trust"
    ∷ [] )
    true refl true refl true refl

cognitiveProfile : OEFElementProfile
cognitiveProfile =
  mkOEFElementProfile
    cognitiveEngagement
    ( "thinking critically"
    ∷ "activating metacognition"
    ∷ "integrating ideas"
    ∷ "justifying decisions"
    ∷ "developing deep discipline understanding"
    ∷ "distributing expertise"
    ∷ [] )
    true refl true refl true refl

behaviouralProfile : OEFElementProfile
behaviouralProfile =
  mkOEFElementProfile
    behaviouralEngagement
    ( "developing academic skills"
    ∷ "identifying opportunities and challenges"
    ∷ "developing multidisciplinary skills"
    ∷ "developing agency"
    ∷ "upholding online learning norms"
    ∷ "supporting and encouraging peers"
    ∷ [] )
    true refl true refl true refl

collaborativeProfile : OEFElementProfile
collaborativeProfile =
  mkOEFElementProfile
    collaborativeEngagement
    ( "learning with peers"
    ∷ "relating to faculty members"
    ∷ "connecting to institutional opportunities"
    ∷ "developing professional networks"
    ∷ [] )
    true refl true refl true refl

emotionalProfile : OEFElementProfile
emotionalProfile =
  mkOEFElementProfile
    emotionalEngagement
    ( "managing expectations"
    ∷ "articulating assumptions"
    ∷ "recognising motivations"
    ∷ "committing to learning"
    ∷ [] )
    true refl true refl true refl

canonicalOEFProfiles : List OEFElementProfile
canonicalOEFProfiles =
  socialProfile
  ∷ cognitiveProfile
  ∷ behaviouralProfile
  ∷ collaborativeProfile
  ∷ emotionalProfile
  ∷ []

------------------------------------------------------------------------
-- Multi-fibre bundles.

record OEFBundle : Set where
  constructor mkOEFBundle
  field
    bundleLabel : String
    bundleElements : List OEFElement
    bundleAllowsOverlap : Bool
    bundleAllowsOverlapIsTrue : bundleAllowsOverlap ≡ true
    bundleNotStudentEssence : Bool
    bundleNotStudentEssenceIsTrue : bundleNotStudentEssence ≡ true

open OEFBundle public

canonicalForumBundle : OEFBundle
canonicalForumBundle =
  mkOEFBundle
    "learning and collaborating in online forum discussions"
    ( cognitiveEngagement
    ∷ behaviouralEngagement
    ∷ collaborativeEngagement
    ∷ socialEngagement
    ∷ [] )
    true
    refl
    true
    refl

canonicalForumBundleHasFourFibres :
  listCount (bundleElements canonicalForumBundle) ≡ 4
canonicalForumBundleHasFourFibres = refl

EngagementOverlapIsSignalNotNoise : Set
EngagementOverlapIsSignalNotNoise =
  bundleAllowsOverlap canonicalForumBundle ≡ true

engagementOverlapIsSignalNotNoise : EngagementOverlapIsSignalNotNoise
engagementOverlapIsSignalNotNoise =
  bundleAllowsOverlapIsTrue canonicalForumBundle

------------------------------------------------------------------------
-- Survey projection and educational hypervoxel.

data FeedbackSurfaceKind : Set where
  voluntaryEndOfCourseComment : FeedbackSurfaceKind
  cleanedCommentSurface : FeedbackSurfaceKind
  humanLabelSurface : FeedbackSurfaceKind
  modelPredictionSurface : FeedbackSurfaceKind
  aggregateVisualisationSurface : FeedbackSurfaceKind

record FeedbackHypervoxel : Set where
  constructor mkFeedbackHypervoxel
  field
    studentSurface : String
    courseSurface : String
    timeSurface : String
    assessmentSurface : String
    teacherRelationSurface : String
    peerRelationSurface : String
    institutionSurface : String
    lifeContextSurface : String
    intersectionalAxisSurface : List String
    feedbackTextSurface : String

open FeedbackHypervoxel public

record SurveyProjection : Set where
  constructor mkSurveyProjection
  field
    projectionSource : FeedbackHypervoxel
    projectionKind : FeedbackSurfaceKind
    projectionText : String
    projectionSparse : Bool
    projectionSparseIsTrue : projectionSparse ≡ true
    projectionSelfSelected : Bool
    projectionSelfSelectedIsTrue : projectionSelfSelected ≡ true
    projectionTimeLocal : Bool
    projectionTimeLocalIsTrue : projectionTimeLocal ≡ true
    projectionNotWholeHypervoxel : Bool
    projectionNotWholeHypervoxelIsTrue : projectionNotWholeHypervoxel ≡ true
    projectionNoHiddenChartRecovery : Bool
    projectionNoHiddenChartRecoveryIsTrue : projectionNoHiddenChartRecovery ≡ true

open SurveyProjection public

canonicalFeedbackHypervoxel : FeedbackHypervoxel
canonicalFeedbackHypervoxel =
  mkFeedbackHypervoxel
    "student surface"
    "course surface"
    "end-of-course time surface"
    "assessment surface"
    "teacher relation surface"
    "peer relation surface"
    "institution surface"
    "life-context surface"
    ( "race"
    ∷ "class"
    ∷ "gender"
    ∷ "disability"
    ∷ "neurotype"
    ∷ "language"
    ∷ "culture"
    ∷ "caring role"
    ∷ "digital access"
    ∷ "prior education"
    ∷ "institutional trust"
    ∷ [] )
    "voluntary end-of-course comment"

canonicalSurveyProjection : SurveyProjection
canonicalSurveyProjection =
  mkSurveyProjection
    canonicalFeedbackHypervoxel
    voluntaryEndOfCourseComment
    "one textual projection of a larger situated student ecology"
    true refl
    true refl
    true refl
    true refl
    true refl

FeedbackIsHypervoxelProjection : Set
FeedbackIsHypervoxelProjection =
  projectionNotWholeHypervoxel canonicalSurveyProjection ≡ true

feedbackIsHypervoxelProjection : FeedbackIsHypervoxelProjection
feedbackIsHypervoxelProjection =
  projectionNotWholeHypervoxelIsTrue canonicalSurveyProjection

------------------------------------------------------------------------
-- Human coding and model prediction.

record HumanCodingDatum : Set where
  constructor mkHumanCodingDatum
  field
    codingCommentSurface : String
    codingHumanAssignedBundle : OEFBundle
    codingInterpretive : Bool
    codingInterpretiveIsTrue : codingInterpretive ≡ true
    codingNotEngagementTruth : Bool
    codingNotEngagementTruthIsTrue : codingNotEngagementTruth ≡ true

open HumanCodingDatum public

record ModelPrediction : Set where
  constructor mkModelPrediction
  field
    predictionInputSurface : String
    predictedBundle : OEFBundle
    sentimentProxy : String
    confidenceSurface : String
    predictionCompiledHumanCoding : Bool
    predictionCompiledHumanCodingIsTrue : predictionCompiledHumanCoding ≡ true
    predictionProxyOnly : Bool
    predictionProxyOnlyIsTrue : predictionProxyOnly ≡ true
    predictionNotStudentMeaning : Bool
    predictionNotStudentMeaningIsTrue : predictionNotStudentMeaning ≡ true
    predictionNotCompleteVoice : Bool
    predictionNotCompleteVoiceIsTrue : predictionNotCompleteVoice ≡ true
    predictionNotPedagogicalAuthority : Bool
    predictionNotPedagogicalAuthorityIsTrue : predictionNotPedagogicalAuthority ≡ true

open ModelPrediction public

canonicalHumanCodingDatum : HumanCodingDatum
canonicalHumanCodingDatum =
  mkHumanCodingDatum
    "I liked learning and collaborating in the online forums."
    canonicalForumBundle
    true refl
    true refl

canonicalModelPrediction : ModelPrediction
canonicalModelPrediction =
  mkModelPrediction
    "cleaned student comment surface"
    canonicalForumBundle
    "sentiment proxy"
    "classification confidence surface"
    true refl
    true refl
    true refl
    true refl
    true refl

HumanLabelCompiledNotRemoved : Set
HumanLabelCompiledNotRemoved =
  predictionCompiledHumanCoding canonicalModelPrediction ≡ true

humanLabelCompiledNotRemoved : HumanLabelCompiledNotRemoved
humanLabelCompiledNotRemoved =
  predictionCompiledHumanCodingIsTrue canonicalModelPrediction

AIClassificationIsProxy : Set
AIClassificationIsProxy =
  predictionProxyOnly canonicalModelPrediction ≡ true

aiClassificationIsProxy : AIClassificationIsProxy
aiClassificationIsProxy =
  predictionProxyOnlyIsTrue canonicalModelPrediction

------------------------------------------------------------------------
-- Study counts and reported classifier metrics.

record ClassifierPerformanceRow : Set where
  constructor mkClassifierPerformanceRow
  field
    performanceElement : OEFElement
    trainingCount : Nat
    precisionHundredths : Nat
    f1Hundredths : Nat
    recallHundredths : Nat
    balancedAccuracyTenthsPercent : Nat

open ClassifierPerformanceRow public

behaviouralPerformance : ClassifierPerformanceRow
behaviouralPerformance =
  mkClassifierPerformanceRow behaviouralEngagement 98 65 51 42 611

cognitivePerformance : ClassifierPerformanceRow
cognitivePerformance =
  mkClassifierPerformanceRow cognitiveEngagement 114 56 54 52 639

emotionalPerformance : ClassifierPerformanceRow
emotionalPerformance =
  mkClassifierPerformanceRow emotionalEngagement 118 86 72 62 931

socialPerformance : ClassifierPerformanceRow
socialPerformance =
  mkClassifierPerformanceRow socialEngagement 28 56 58 60 722

collaborativePerformance : ClassifierPerformanceRow
collaborativePerformance =
  mkClassifierPerformanceRow collaborativeEngagement 25 87 70 58 561

canonicalPerformanceRows : List ClassifierPerformanceRow
canonicalPerformanceRows =
  behaviouralPerformance
  ∷ cognitivePerformance
  ∷ emotionalPerformance
  ∷ socialPerformance
  ∷ collaborativePerformance
  ∷ []

record PaperStudySurface : Set where
  constructor mkPaperStudySurface
  field
    labelledTrainingFeedbackSentiments : Nat
    laterTestingFeedbackSentiments : Nat
    overallAccuracyPercent : Nat
    performanceRows : List ClassifierPerformanceRow
    categorySpecificErrorVisible : Bool
    categorySpecificErrorVisibleIsTrue : categorySpecificErrorVisible ≡ true
    classImbalanceRecorded : Bool
    classImbalanceRecordedIsTrue : classImbalanceRecorded ≡ true
    ambiguitySarcasmDomainLanguageRecorded : Bool
    ambiguitySarcasmDomainLanguageRecordedIsTrue : ambiguitySarcasmDomainLanguageRecorded ≡ true
    annotationBiasOpen : Bool
    annotationBiasOpenIsTrue : annotationBiasOpen ≡ true
    singleRegionalUniversityScope : Bool
    singleRegionalUniversityScopeIsTrue : singleRegionalUniversityScope ≡ true

open PaperStudySurface public

canonicalPaperStudySurface : PaperStudySurface
canonicalPaperStudySurface =
  mkPaperStudySurface
    383
    311
    76
    canonicalPerformanceRows
    true refl
    true refl
    true refl
    true refl
    true refl

canonicalTrainingCount :
  labelledTrainingFeedbackSentiments canonicalPaperStudySurface ≡ 383
canonicalTrainingCount = refl

canonicalTestingCount :
  laterTestingFeedbackSentiments canonicalPaperStudySurface ≡ 311
canonicalTestingCount = refl

canonicalOverallAccuracy :
  overallAccuracyPercent canonicalPaperStudySurface ≡ 76
canonicalOverallAccuracy = refl

canonicalBehaviouralRecall :
  recallHundredths behaviouralPerformance ≡ 42
canonicalBehaviouralRecall = refl

------------------------------------------------------------------------
-- Residual decomposition.

data FeedbackResidualKind : Set where
  samplingResidual : FeedbackResidualKind
  nonresponseResidual : FeedbackResidualKind
  annotationResidual : FeedbackResidualKind
  classificationResidual : FeedbackResidualKind
  semanticResidual : FeedbackResidualKind
  multilabelCompressionResidual : FeedbackResidualKind
  ecologicalResidual : FeedbackResidualKind
  intersectionalResidual : FeedbackResidualKind
  temporalResidual : FeedbackResidualKind
  pedagogicalResidual : FeedbackResidualKind

canonicalFeedbackResidualKinds : List FeedbackResidualKind
canonicalFeedbackResidualKinds =
  samplingResidual
  ∷ nonresponseResidual
  ∷ annotationResidual
  ∷ classificationResidual
  ∷ semanticResidual
  ∷ multilabelCompressionResidual
  ∷ ecologicalResidual
  ∷ intersectionalResidual
  ∷ temporalResidual
  ∷ pedagogicalResidual
  ∷ []

canonicalFeedbackResidualKindCount :
  listCount canonicalFeedbackResidualKinds ≡ 10
canonicalFeedbackResidualKindCount = refl

------------------------------------------------------------------------
-- Claim routes and fail-closed boundaries.

data FeedbackClaimRoute : Set where
  candidateFeedbackProxyRoute : FeedbackClaimRoute
  modelEqualsStudentMeaningRoute : FeedbackClaimRoute
  surveyEqualsCompleteVoiceRoute : FeedbackClaimRoute
  respondentsEqualCohortRoute : FeedbackClaimRoute
  missingCategoryEqualsMissingEngagementRoute : FeedbackClaimRoute
  sentimentEqualsWellbeingRoute : FeedbackClaimRoute
  aggregateEqualsIndividualRoute : FeedbackClaimRoute
  endpointEqualsTrajectoryRoute : FeedbackClaimRoute
  oefEqualsWholeEcologyRoute : FeedbackClaimRoute
  dashboardEqualsPedagogicalAuthorityRoute : FeedbackClaimRoute

AdmissibleFeedbackClaimRoute : FeedbackClaimRoute → Set
AdmissibleFeedbackClaimRoute candidateFeedbackProxyRoute = ⊤
AdmissibleFeedbackClaimRoute modelEqualsStudentMeaningRoute = Never
AdmissibleFeedbackClaimRoute surveyEqualsCompleteVoiceRoute = Never
AdmissibleFeedbackClaimRoute respondentsEqualCohortRoute = Never
AdmissibleFeedbackClaimRoute missingCategoryEqualsMissingEngagementRoute = Never
AdmissibleFeedbackClaimRoute sentimentEqualsWellbeingRoute = Never
AdmissibleFeedbackClaimRoute aggregateEqualsIndividualRoute = Never
AdmissibleFeedbackClaimRoute endpointEqualsTrajectoryRoute = Never
AdmissibleFeedbackClaimRoute oefEqualsWholeEcologyRoute = Never
AdmissibleFeedbackClaimRoute dashboardEqualsPedagogicalAuthorityRoute = Never

candidateFeedbackProxyRouteAdmissible :
  AdmissibleFeedbackClaimRoute candidateFeedbackProxyRoute
candidateFeedbackProxyRouteAdmissible = tt

modelEqualsStudentMeaningBlocked :
  AdmissibleFeedbackClaimRoute modelEqualsStudentMeaningRoute → Never
modelEqualsStudentMeaningBlocked ()

surveyEqualsCompleteVoiceBlocked :
  AdmissibleFeedbackClaimRoute surveyEqualsCompleteVoiceRoute → Never
surveyEqualsCompleteVoiceBlocked ()

respondentsEqualCohortBlocked :
  AdmissibleFeedbackClaimRoute respondentsEqualCohortRoute → Never
respondentsEqualCohortBlocked ()

missingCategoryEqualsMissingEngagementBlocked :
  AdmissibleFeedbackClaimRoute missingCategoryEqualsMissingEngagementRoute → Never
missingCategoryEqualsMissingEngagementBlocked ()

sentimentEqualsWellbeingBlocked :
  AdmissibleFeedbackClaimRoute sentimentEqualsWellbeingRoute → Never
sentimentEqualsWellbeingBlocked ()

aggregateEqualsIndividualBlocked :
  AdmissibleFeedbackClaimRoute aggregateEqualsIndividualRoute → Never
aggregateEqualsIndividualBlocked ()

endpointEqualsTrajectoryBlocked :
  AdmissibleFeedbackClaimRoute endpointEqualsTrajectoryRoute → Never
endpointEqualsTrajectoryBlocked ()

oefEqualsWholeEcologyBlocked :
  AdmissibleFeedbackClaimRoute oefEqualsWholeEcologyRoute → Never
oefEqualsWholeEcologyBlocked ()

dashboardEqualsPedagogicalAuthorityBlocked :
  AdmissibleFeedbackClaimRoute dashboardEqualsPedagogicalAuthorityRoute → Never
dashboardEqualsPedagogicalAuthorityBlocked ()

------------------------------------------------------------------------
-- Canonical aggregate.

record OEFMultiFibreFeedbackHyperfabric : Set where
  constructor mkOEFMultiFibreFeedbackHyperfabric
  field
    sourceReference : PaperReference
    sourceReferenceIsCanonical : sourceReference ≡ canonicalPaperReference
    oefElements : List OEFElement
    oefElementsAreCanonical : oefElements ≡ canonicalOEFElements
    oefProfiles : List OEFElementProfile
    oefProfilesAreCanonical : oefProfiles ≡ canonicalOEFProfiles
    forumMultiFibreBundle : OEFBundle
    forumMultiFibreBundleIsCanonical : forumMultiFibreBundle ≡ canonicalForumBundle
    surveyProjection : SurveyProjection
    surveyProjectionIsCanonical : surveyProjection ≡ canonicalSurveyProjection
    humanCodingDatum : HumanCodingDatum
    humanCodingDatumIsCanonical : humanCodingDatum ≡ canonicalHumanCodingDatum
    modelPrediction : ModelPrediction
    modelPredictionIsCanonical : modelPrediction ≡ canonicalModelPrediction
    paperStudySurface : PaperStudySurface
    paperStudySurfaceIsCanonical : paperStudySurface ≡ canonicalPaperStudySurface
    residualKinds : List FeedbackResidualKind
    residualKindsAreCanonical : residualKinds ≡ canonicalFeedbackResidualKinds
    claimRoute : FeedbackClaimRoute
    claimRouteIsCandidate : claimRoute ≡ candidateFeedbackProxyRoute
    claimRouteAdmissible : AdmissibleFeedbackClaimRoute claimRoute
    multiLabelPreserved : Bool
    multiLabelPreservedIsTrue : multiLabelPreserved ≡ true
    humanCodeInterpretive : Bool
    humanCodeInterpretiveIsTrue : humanCodeInterpretive ≡ true
    modelPredictionProxyOnly : Bool
    modelPredictionProxyOnlyIsTrue : modelPredictionProxyOnly ≡ true
    aggregateNotIndividual : Bool
    aggregateNotIndividualIsTrue : aggregateNotIndividual ≡ true
    missingCategoryNotMissingEngagement : Bool
    missingCategoryNotMissingEngagementIsTrue : missingCategoryNotMissingEngagement ≡ true
    humanReviewRequired : Bool
    humanReviewRequiredIsTrue : humanReviewRequired ≡ true
    reading : String

open OEFMultiFibreFeedbackHyperfabric public

canonicalOEFMultiFibreFeedbackHyperfabric :
  OEFMultiFibreFeedbackHyperfabric
canonicalOEFMultiFibreFeedbackHyperfabric =
  mkOEFMultiFibreFeedbackHyperfabric
    canonicalPaperReference refl
    canonicalOEFElements refl
    canonicalOEFProfiles refl
    canonicalForumBundle refl
    canonicalSurveyProjection refl
    canonicalHumanCodingDatum refl
    canonicalModelPrediction refl
    canonicalPaperStudySurface refl
    canonicalFeedbackResidualKinds refl
    candidateFeedbackProxyRoute refl tt
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "Student feedback is a sparse, self-selected, time-local projection of a multi-fibred educational hyperfabric. OEF and NLP may organise the projection and expose candidate overlaps and residuals; contextual human review and governance are required before pedagogical action."

OEFIsMultiFibred : Set
OEFIsMultiFibred =
  multiLabelPreserved canonicalOEFMultiFibreFeedbackHyperfabric ≡ true

oefIsMultiFibred : OEFIsMultiFibred
oefIsMultiFibred =
  multiLabelPreservedIsTrue canonicalOEFMultiFibreFeedbackHyperfabric

AggregateVisualisationNotIndividualTruth : Set
AggregateVisualisationNotIndividualTruth =
  aggregateNotIndividual canonicalOEFMultiFibreFeedbackHyperfabric ≡ true

aggregateVisualisationNotIndividualTruth :
  AggregateVisualisationNotIndividualTruth
aggregateVisualisationNotIndividualTruth =
  aggregateNotIndividualIsTrue canonicalOEFMultiFibreFeedbackHyperfabric

MissingClassificationNotMissingEngagement : Set
MissingClassificationNotMissingEngagement =
  missingCategoryNotMissingEngagement canonicalOEFMultiFibreFeedbackHyperfabric ≡ true

missingClassificationNotMissingEngagement :
  MissingClassificationNotMissingEngagement
missingClassificationNotMissingEngagement =
  missingCategoryNotMissingEngagementIsTrue canonicalOEFMultiFibreFeedbackHyperfabric
