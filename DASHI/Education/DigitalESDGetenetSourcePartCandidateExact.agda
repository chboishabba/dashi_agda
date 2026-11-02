module DASHI.Education.DigitalESDGetenetSourcePartCandidateExact where

------------------------------------------------------------------------
-- REAL PUBLISHED PAPER; CANDIDATE RETROSPECTIVE RECONSTRUCTION
--
-- Getenet, S.; Burke, K.; Fanshawe, M.; Brown, A. (2026).
-- "Supporting online learning in teacher education: student-identified
-- strategies and social constructivist implications."
-- Distance Education, DOI: 10.1080/01587919.2026.2669288.
-- Published online 20 May 2026.
-- Original published article, sections Introduction, Method, Participants,
-- Data collection, Data analysis, Author positionality, Results, Conclusion.
--
-- Counts and themes below are PAPER-REPORTED, not independently reviewed
-- SLR source spans and not DASHI sustainability findings. The published
-- paper is source authority for its original reported work only.
-- Existing original-study source and five strategies are reused, not copied
-- into a competing source registry. The Attr view has the same exact DOI.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

import DASHI.Biology.EducationCorpusSourceRegistry as Source
import DASHI.Biology.StudentIdentifiedSupportStrategiesBridge as Support
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World

getenetSource : Attr.AttributedSource
getenetSource = Attr.mkDOISource
  "Seyum Getenet; Katie Burke; Melissa Fanshawe; Alice Brown"
  (Source.paperTitle Source.onlineSupportStrategiesPaper)
  (Source.paperJournal Source.onlineSupportStrategiesPaper)
  "2026"
  (Source.paperDOI Source.onlineSupportStrategiesPaper)
  "https://doi.org/10.1080/01587919.2026.2669288"
  Attr.academicArticleSource
  "Original reported study; pending exact full-text SLR evidence admission"
  Attr.publicAttribution

doiWeld :
  Attr.doiState getenetSource ≡
  Attr.doiRecorded (Source.paperDOI Source.onlineSupportStrategiesPaper)
doiWeld = refl

paperTitleWeld :
  Attr.sourceTitle getenetSource ≡
  Source.paperTitle Source.onlineSupportStrategiesPaper
paperTitleWeld = refl

data OriginalStudy : Set where
  getenetStudy : OriginalStudy

-- The candidate full-paper decomposition: parts are not just five themes.
-- No assertion is made that every sentence has been independently audited.
data StudyPart : OriginalStudy → Set where
  originalQuestions : StudyPart getenetStudy
  socialConstructivistTheory : StudyPart getenetStudy
  eligiblePopulationAndSampling : StudyPart getenetStudy
  openResponseInstrument : StudyPart getenetStudy
  codingAndThematicMethod : StudyPart getenetStudy
  researcherPositionality : StudyPart getenetStudy
  autonomyAndFlexibility : StudyPart getenetStudy
  accessibleResources : StudyPart getenetStudy
  communityAndInteraction : StudyPart getenetStudy
  scaffoldingAndGuidance : StudyPart getenetStudy
  selfOrganisation : StudyPart getenetStudy
  negativeAndOutlierResponses : StudyPart getenetStudy
  boundedOriginalInterpretation : StudyPart getenetStudy
  unobservedAndExcludedPositions : StudyPart getenetStudy
  researcherRecomposition : StudyPart getenetStudy

allStudyParts : List (StudyPart getenetStudy)
allStudyParts =
  originalQuestions ∷ socialConstructivistTheory ∷
  eligiblePopulationAndSampling ∷ openResponseInstrument ∷
  codingAndThematicMethod ∷ researcherPositionality ∷
  autonomyAndFlexibility ∷ accessibleResources ∷
  communityAndInteraction ∷ scaffoldingAndGuidance ∷
  selfOrganisation ∷ negativeAndOutlierResponses ∷
  boundedOriginalInterpretation ∷ unobservedAndExcludedPositions ∷
  researcherRecomposition ∷ []

partName : StudyPart getenetStudy → String
partName originalQuestions = "three original research questions"
partName socialConstructivistTheory = "social constructivist interpretation"
partName eligiblePopulationAndSampling = "eligible/responding pre-service teachers"
partName openResponseInstrument = "single-idea open-response question"
partName codingAndThematicMethod = "inductive thematic coding procedure"
partName researcherPositionality = "author positionality and coding negotiation"
partName autonomyAndFlexibility = "learner autonomy and flexibility"
partName accessibleResources = "accessibility and centralised resources"
partName communityAndInteraction = "interaction, community and support"
partName scaffoldingAndGuidance = "scaffolding and clear guidance"
partName selfOrganisation = "organisational self-management"
partName negativeAndOutlierResponses = "negative and outlier responses"
partName boundedOriginalInterpretation = "bounded interpretive conclusion"
partName unobservedAndExcludedPositions = "unobserved and nonresponding positions"
partName researcherRecomposition = "retrospective interpretation of this study"

sectionName : StudyPart getenetStudy → String
sectionName originalQuestions = "Introduction: three research questions"
sectionName socialConstructivistTheory = "Social constructivism: theoretical foundations"
sectionName eligiblePopulationAndSampling = "Method: Participants"
sectionName openResponseInstrument = "Method: Data collection"
sectionName codingAndThematicMethod = "Method: Data analysis"
sectionName researcherPositionality = "Method: Author positionality"
sectionName autonomyAndFlexibility = "Results: Theme 1"
sectionName accessibleResources = "Results: Theme 2"
sectionName communityAndInteraction = "Results: Theme 3"
sectionName scaffoldingAndGuidance = "Results: Theme 4"
sectionName selfOrganisation = "Results: organizational strategy theme"
sectionName negativeAndOutlierResponses = "Results: sixth theme and outliers"
sectionName boundedOriginalInterpretation = "Conclusion"
sectionName unobservedAndExcludedPositions = "Method: Participants; response noncoverage"
sectionName researcherRecomposition = "DASHI candidate retrospective re-reading"

parts : (s : OriginalStudy) → List (StudyPart s)
parts getenetStudy = allStudyParts

partListed : (s : OriginalStudy) (p : StudyPart s) → p ∈ parts s
partListed getenetStudy originalQuestions = here refl
partListed getenetStudy socialConstructivistTheory = there (here refl)
partListed getenetStudy eligiblePopulationAndSampling = there (there (here refl))
partListed getenetStudy openResponseInstrument = there (there (there (here refl)))
partListed getenetStudy codingAndThematicMethod = there (there (there (there (here refl))))
partListed getenetStudy researcherPositionality = there (there (there (there (there (here refl)))))
partListed getenetStudy autonomyAndFlexibility = there (there (there (there (there (there (here refl))))))
partListed getenetStudy accessibleResources = there (there (there (there (there (there (there (here refl)))))))
partListed getenetStudy communityAndInteraction = there (there (there (there (there (there (there (there (here refl))))))))
partListed getenetStudy scaffoldingAndGuidance = there (there (there (there (there (there (there (there (there (here refl)))))))))
partListed getenetStudy selfOrganisation = there (there (there (there (there (there (there (there (there (there (here refl))))))))))
partListed getenetStudy negativeAndOutlierResponses = there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))
partListed getenetStudy boundedOriginalInterpretation = there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))
partListed getenetStudy unobservedAndExcludedPositions = there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))
partListed getenetStudy researcherRecomposition = there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))

-- Seven test axes are a versioned *example subfamily*, not the full n-axis
-- ontology. They can be refined/extended without an ESD axis-count limit.
data CandidateAxis : Set where
  pedagogyAndLearning : CandidateAxis
  participantVoice : CandidateAxis
  effectiveDisabilityAccess : CandidateAxis
  consequentialDecisionAuthority : CandidateAxis
  materialEcologicalBurden : CandidateAxis
  temporalInstitutionalDurability : CandidateAxis
  researcherEpistemicPosition : CandidateAxis

allCandidateAxes : List CandidateAxis
allCandidateAxes =
  pedagogyAndLearning ∷ participantVoice ∷ effectiveDisabilityAccess ∷
  consequentialDecisionAuthority ∷ materialEcologicalBurden ∷
  temporalInstitutionalDurability ∷ researcherEpistemicPosition ∷ []

axisName : CandidateAxis → String
axisName pedagogyAndLearning = "pedagogy and learning"
axisName participantVoice = "participant voice"
axisName effectiveDisabilityAccess = "effective disability-specific access"
axisName consequentialDecisionAuthority = "consequential participant decision authority"
axisName materialEcologicalBurden = "material and ecological burden"
axisName temporalInstitutionalDurability = "durability and longitudinal outcomes"
axisName researcherEpistemicPosition = "researcher position and inference authority"

axisListed : (a : CandidateAxis) → a ∈ allCandidateAxes
axisListed pedagogyAndLearning = here refl
axisListed participantVoice = there (here refl)
axisListed effectiveDisabilityAccess = there (there (here refl))
axisListed consequentialDecisionAuthority = there (there (there (here refl)))
axisListed materialEcologicalBurden = there (there (there (there (here refl))))
axisListed temporalInstitutionalDurability = there (there (there (there (there (here refl)))))
axisListed researcherEpistemicPosition = there (there (there (there (there (there (here refl))))))

-- This reconstruction has NOT obtained independent reviewed SourceAudit
-- membership or same-span SLR evidence. Therefore the 'directReviewed'
-- constructor is unavailable in this instance.
studyScope : World.StudyWorldScope
studyScope = World.study-world-scope
  OriginalStudy
  StudyPart
  CandidateAxis
  (λ _ → getenetSource)
  (λ _ → Source.paperKey Source.onlineSupportStrategiesPaper)
  (λ { getenetStudy → partName })
  axisName
  (getenetStudy ∷ [])
  (λ { getenetStudy → here refl })
  parts
  partListed
  allCandidateAxes
  axisListed
  (λ _ _ _ _ → ⊥)

-- Real author-reported source measurements. 885 is the number of survey
-- invitations, not additional respondents. 45 instances were coded twice;
-- do not sum theme frequencies as independent unique people.
record AuthorReportedSample : Set where
  constructor author-reported-sample
  field
    originalPaper : Source.PaperReference
    originalPaperExact : originalPaper ≡ Source.onlineSupportStrategiesPaper
    surveyInvitations : Nat
    invitationsAre885 : surveyInvitations ≡ 885
    analysedResponses : Nat
    responsesAre584 : analysedResponses ≡ 584
    doubleCodedResponses : Nat
    doubleCodingIs45 : doubleCodedResponses ≡ 45
    sourceMethodSection : String
    notAnSLRReviewReceipt : String

sourceReportedSample : AuthorReportedSample
sourceReportedSample = author-reported-sample
  Source.onlineSupportStrategiesPaper refl
  885 refl 584 refl 45 refl
  "Method: Participants, Data collection, Data analysis"
  "Published author-reported numbers; no independently signed full-text packet"

-- Author-reported, not reviewer-admitted, where supported by the specified
-- published section. Other axis questions remain genuinely unpaid.
partAxisAssessment :
  (p : StudyPart getenetStudy) (a : CandidateAxis) →
  World.PartAxisAccounting studyScope getenetStudy p a
partAxisAssessment originalQuestions pedagogyAndLearning =
  World.sourceReportedPendingReview
    "Introduction: research questions"
    "Three stated questions about PST helpful ideas, constructivism and course design"
    "Exact passage/SLR reviewer admission pending"
partAxisAssessment eligiblePopulationAndSampling participantVoice =
  World.sourceReportedPendingReview
    "Method: Participants and Data collection"
    "885 invited, 584 responses over 12 offerings in 2019-2024"
    "Sampling, eligible nonresponse and exact reviewed span pending"
partAxisAssessment openResponseInstrument participantVoice =
  World.sourceReportedPendingReview
    "Method: Data collection"
    "Open-ended one-helpful-idea question; no student governing decision demonstrated"
    "Exact review and source revision pending"
partAxisAssessment codingAndThematicMethod pedagogyAndLearning =
  World.sourceReportedPendingReview
    "Method: Data analysis"
    "Inductive Braun-Clarke six-phase thematic analysis; 45 responses double-coded"
    "Exact table, codebook and review packet pending"
partAxisAssessment researcherPositionality researcherEpistemicPosition =
  World.sourceReportedPendingReview
    "Method: Author positionality"
    "Researchers include teacher educators; two independently coded and negotiated"
    "Independent positionality and source review pending"
partAxisAssessment autonomyAndFlexibility pedagogyAndLearning =
  World.sourceReportedPendingReview (sectionName autonomyAndFlexibility)
    "Source reports N=101 coded responses" "Original denominator/quote review pending"
partAxisAssessment accessibleResources pedagogyAndLearning =
  World.sourceReportedPendingReview (sectionName accessibleResources)
    "Source reports N=126 coded responses" "Original denominator/quote review pending"
partAxisAssessment communityAndInteraction pedagogyAndLearning =
  World.sourceReportedPendingReview (sectionName communityAndInteraction)
    "Source reports N=146 coded responses" "Original denominator/quote review pending"
partAxisAssessment scaffoldingAndGuidance pedagogyAndLearning =
  World.sourceReportedPendingReview (sectionName scaffoldingAndGuidance)
    "Source reports N=100 coded responses" "Original denominator/quote review pending"
partAxisAssessment negativeAndOutlierResponses pedagogyAndLearning =
  World.sourceReportedPendingReview (sectionName negativeAndOutlierResponses)
    "Article reports sixth contrasting theme with N=15 outliers and N=26 challenges"
    "Check distinct statuses and author tables before reuse"
partAxisAssessment p a =
  World.unmeasuredForQuestion
    (axisName a)
    ("Review whether source evidence addresses " ++pending)
  where
    postulate ++pending : String

-- The fallback intentionally has NO invented empirical findings. The
-- generic missing status above is a review query, not a proved absent effect.
studyWorld : World.AccountedStudyWorld studyScope
studyWorld = World.accounted-study-world
  (λ { getenetStudy p a → partAxisAssessment p a })
