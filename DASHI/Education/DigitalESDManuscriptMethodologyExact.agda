module DASHI.Education.DigitalESDManuscriptMethodologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper
import DASHI.Education.DigitalESDStructuredSearchExact as Search
import DASHI.Education.DigitalESDManuscriptDependencyPaymentAdapterExact as Payment
import DASHI.Education.DigitalESDPrimarySourceMethodologyAtlasExact as Primary
import DASHI.Education.DigitalInnovationESDTransformationExact as Transformation
import DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapExact as Literature
import DASHI.Education.DigitalESDParticipantGovernanceContextTransferExact as Governance

------------------------------------------------------------------------
-- PAPER-FACING METHODOLOGY
--
-- This owner does not introduce a new review calculus. It specializes the
-- already-declared integrative conceptual review into a manuscript method that
-- can be reported transparently: questions -> structured search -> eligibility
-- -> extraction -> source/scope matrix -> reciprocal synthesis -> limitations.
--
-- Whittemore/Knafl, SANRA, PRISMA-S and PRESS remain method sources in the
-- existing Paper/Search owners. The institutional sources added in the Primary
-- atlas pay content/context coordinates only; they do not execute the method.
------------------------------------------------------------------------

currentPaperType : Paper.PaperType
currentPaperType = Paper.currentPaperType

------------------------------------------------------------------------
-- Research questions.
------------------------------------------------------------------------

data ManuscriptResearchQuestion : Set where
  digitalEducationBuildsESDCapacityRQ : ManuscriptResearchQuestion
  transformationBeyondTechnologyUseRQ : ManuscriptResearchQuestion
  sustainabilityConstrainsDigitalEducationRQ : ManuscriptResearchQuestion
  participantAgencyAndGovernanceRQ : ManuscriptResearchQuestion
  durabilityAndLongitudinalTransformationRQ : ManuscriptResearchQuestion

researchQuestions : List ManuscriptResearchQuestion
researchQuestions =
  digitalEducationBuildsESDCapacityRQ
  ∷ transformationBeyondTechnologyUseRQ
  ∷ sustainabilityConstrainsDigitalEducationRQ
  ∷ participantAgencyAndGovernanceRQ
  ∷ durabilityAndLongitudinalTransformationRQ
  ∷ []

researchQuestionCount : Nat
researchQuestionCount = 5

researchQuestionReference : ManuscriptResearchQuestion → String
researchQuestionReference digitalEducationBuildsESDCapacityRQ =
  "RQ1: Through what pedagogical, curricular, competence, learning-environment and institutional mechanisms can digital education build ESD capacity?"
researchQuestionReference transformationBeyondTechnologyUseRQ =
  "RQ2: Under what conditions does digital innovation support educational/system transformation rather than technology adoption or task performance alone?"
researchQuestionReference sustainabilityConstrainsDigitalEducationRQ =
  "RQ3: How should environmental, social, economic, lifecycle, circularity and infrastructure considerations constrain digital education itself?"
researchQuestionReference participantAgencyAndGovernanceRQ =
  "RQ4: How should learner/participant voice, epistemic agency and governance enter digital-ESD design without inflating literature, consent or consultation into local authority?"
researchQuestionReference durabilityAndLongitudinalTransformationRQ =
  "RQ5: What evidence and conditions bear on durability, institutionalisation, context transfer and longitudinal transformation, and which claims remain future empirical debt?"

------------------------------------------------------------------------
-- Integrative-review process stages.
------------------------------------------------------------------------

data IntegrativeReviewStage : Set where
  problemIdentification : IntegrativeReviewStage
  literatureSearch : IntegrativeReviewStage
  dataEvaluation : IntegrativeReviewStage
  dataAnalysisAndSynthesis : IntegrativeReviewStage
  presentationAndLimitations : IntegrativeReviewStage

canonicalIntegrativeReviewStages : List IntegrativeReviewStage
canonicalIntegrativeReviewStages =
  problemIdentification
  ∷ literatureSearch
  ∷ dataEvaluation
  ∷ dataAnalysisAndSynthesis
  ∷ presentationAndLimitations
  ∷ []

methodSourceAtlas : Attr.AttributedSourceAtlas
methodSourceAtlas = Paper.paperMethodSourceAtlas

structuredSearchMethodAtlas : Attr.AttributedSourceAtlas
structuredSearchMethodAtlas = Search.structuredSearchMethodAtlas

primarySourceExtensionAtlas : Attr.AttributedSourceAtlas
primarySourceExtensionAtlas = Primary.primaryMethodologySourceAtlas

structuredSearchLedger : Search.StructuredSearchLedger
structuredSearchLedger = Search.canonicalStructuredSearchLedger

manuscriptDependencyGraph = Payment.canonicalManuscriptDependencyGraph

------------------------------------------------------------------------
-- Inclusion / exclusion policy.
--
-- Eligibility is question- and role-relative. A source need not be an
-- empirical intervention study to be included in an integrative review, but it
-- must contribute a declared role and retain the population/context/time and
-- evidentiary limitations needed by its consumer.
------------------------------------------------------------------------

data EvidenceRole : Set where
  empiricalOutcomeEvidence : EvidenceRole
  reviewSynthesisEvidence : EvidenceRole
  methodologyEvidence : EvidenceRole
  institutionalFrameworkEvidence : EvidenceRole
  infrastructureLifecycleEvidence : EvidenceRole
  participantGovernanceEvidence : EvidenceRole
  longitudinalDurabilityEvidence : EvidenceRole
  contextualComparatorEvidence : EvidenceRole

record EligibilityPolicy : Set where
  constructor eligibility-policy
  field
    mustAddressDeclaredResearchQuestion : Bool
    mustAddressDeclaredResearchQuestionIsTrue :
      mustAddressDeclaredResearchQuestion ≡ true
    mustRetainSourceRole : Bool
    mustRetainSourceRoleIsTrue : mustRetainSourceRole ≡ true
    mustRetainPopulationOrSystemContext : Bool
    mustRetainPopulationOrSystemContextIsTrue :
      mustRetainPopulationOrSystemContext ≡ true
    mustRetainTimeHorizon : Bool
    mustRetainTimeHorizonIsTrue : mustRetainTimeHorizon ≡ true
    mustRetainLimitationsAndTransferBoundary : Bool
    mustRetainLimitationsAndTransferBoundaryIsTrue :
      mustRetainLimitationsAndTransferBoundary ≡ true
    citationAloneCreatesEligibility : Bool
    citationAloneCreatesEligibilityIsFalse :
      citationAloneCreatesEligibility ≡ false
    acquisitionAloneCreatesInclusion : Bool
    acquisitionAloneCreatesInclusionIsFalse :
      acquisitionAloneCreatesInclusion ≡ false

open EligibilityPolicy public

canonicalEligibilityPolicy : EligibilityPolicy
canonicalEligibilityPolicy =
  eligibility-policy
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Structured extraction schema.
------------------------------------------------------------------------

data ExtractionCoordinate : Set where
  sourceIdentityCoordinate : ExtractionCoordinate
  sourceKindAndRoleCoordinate : ExtractionCoordinate
  publicationDateCoordinate : ExtractionCoordinate
  populationEducationLevelCoordinate : ExtractionCoordinate
  jurisdictionInstitutionContextCoordinate : ExtractionCoordinate
  digitalTechnologyOrPracticeCoordinate : ExtractionCoordinate
  pedagogyCurriculumCompetenceCoordinate : ExtractionCoordinate
  sustainabilityDimensionCoordinate : ExtractionCoordinate
  studyOrReviewDesignCoordinate : ExtractionCoordinate
  outcomeOrClaimCoordinate : ExtractionCoordinate
  timeHorizonCoordinate : ExtractionCoordinate
  lifecycleBoundaryCoordinate : ExtractionCoordinate
  circularityRepairabilityCoordinate : ExtractionCoordinate
  participantAgencyAuthorityCoordinate : ExtractionCoordinate
  interoperabilityGovernanceCoordinate : ExtractionCoordinate
  sameObjectStatusCoordinate : ExtractionCoordinate
  contextTransferCoordinate : ExtractionCoordinate
  uncertaintyLimitationCoordinate : ExtractionCoordinate

canonicalExtractionSchema : List ExtractionCoordinate
canonicalExtractionSchema =
  sourceIdentityCoordinate
  ∷ sourceKindAndRoleCoordinate
  ∷ publicationDateCoordinate
  ∷ populationEducationLevelCoordinate
  ∷ jurisdictionInstitutionContextCoordinate
  ∷ digitalTechnologyOrPracticeCoordinate
  ∷ pedagogyCurriculumCompetenceCoordinate
  ∷ sustainabilityDimensionCoordinate
  ∷ studyOrReviewDesignCoordinate
  ∷ outcomeOrClaimCoordinate
  ∷ timeHorizonCoordinate
  ∷ lifecycleBoundaryCoordinate
  ∷ circularityRepairabilityCoordinate
  ∷ participantAgencyAuthorityCoordinate
  ∷ interoperabilityGovernanceCoordinate
  ∷ sameObjectStatusCoordinate
  ∷ contextTransferCoordinate
  ∷ uncertaintyLimitationCoordinate
  ∷ []

------------------------------------------------------------------------
-- Synthesis axes.
------------------------------------------------------------------------

data ReciprocityDirection : Set where
  digitalEducationToESDCapacity : ReciprocityDirection
  sustainabilityToDigitalEducationConstraint : ReciprocityDirection
  bidirectionalReciprocalRelation : ReciprocityDirection

data TransformationStatus : Set where
  technologyAdoptionOnly : TransformationStatus
  learningOrPerformanceChange : TransformationStatus
  institutionalOrSystemTransformation : TransformationStatus
  transformationStatusUnresolved : TransformationStatus

data EvidencePaymentStatus : Set where
  sourceRolePaid : EvidencePaymentStatus
  contextualCoordinatePaid : EvidencePaymentStatus
  sameObjectCoordinatePaid : EvidencePaymentStatus
  explicitResidualRetained : EvidencePaymentStatus

record SynthesisCell : Set where
  constructor synthesis-cell
  field
    researchQuestion : ManuscriptResearchQuestion
    evidenceRole : EvidenceRole
    reciprocityDirection : ReciprocityDirection
    transformationStatus : TransformationStatus
    paymentStatus : EvidencePaymentStatus
    sourceReference : String
    populationContextReference : String
    timeHorizonReference : String
    limitationReference : String

open SynthesisCell public

------------------------------------------------------------------------
-- Newly acquired primary-source receipts.
------------------------------------------------------------------------

record SourceReceipt : Set where
  constructor source-receipt
  field
    source : Attr.AttributedSource
    acquiredOn : String
    sourceRole : String
    observed : Bool
    observedIsTrue : observed ≡ true

open SourceReceipt public

unescoESD2030RoadmapReceipt : SourceReceipt
unescoESD2030RoadmapReceipt =
  source-receipt
    Primary.unescoESD2030RoadmapSource
    "2026-09-16"
    "primary institutional ESD implementation framework / system-transformation context"
    true refl

unescoESD2030MidtermReceipt : SourceReceipt
unescoESD2030MidtermReceipt =
  source-receipt
    Primary.unescoESD2030MidtermSource
    "2026-09-16"
    "primary programme-level evaluation / activity-versus-system-transformation context"
    true refl

oecdDigitalEducationOutlook2026Receipt : SourceReceipt
oecdDigitalEducationOutlook2026Receipt =
  source-receipt
    Primary.oecdDigitalEducationOutlook2026Source
    "2026-09-16"
    "primary institutional evidence/policy synthesis / performance-versus-learning and pedagogical-condition context"
    true refl

------------------------------------------------------------------------
-- Consumer-facing separations strengthened by the primary sources.
------------------------------------------------------------------------

data ActivityLevelDeterminesSystemTransformation : Set where

data TaskPerformanceDeterminesLearning : Set where

data SearchClosureEqualsEvidenceSynthesis : Set where

data PrimarySourceAcquisitionCreatesIncludedStudy : Set where

data MethodCitationCreatesExecution : Set where

data InstitutionalFrameworkCreatesLocalAuthority : Set where

activityDoesNotDetermineSystemTransformation :
  ActivityLevelDeterminesSystemTransformation → ⊥
activityDoesNotDetermineSystemTransformation ()

taskPerformanceDoesNotDetermineLearning : TaskPerformanceDeterminesLearning → ⊥
taskPerformanceDoesNotDetermineLearning ()

searchClosureDoesNotEqualEvidenceSynthesis :
  SearchClosureEqualsEvidenceSynthesis → ⊥
searchClosureDoesNotEqualEvidenceSynthesis ()

primarySourceAcquisitionDoesNotCreateIncludedStudy :
  PrimarySourceAcquisitionCreatesIncludedStudy → ⊥
primarySourceAcquisitionDoesNotCreateIncludedStudy ()

methodCitationDoesNotCreateExecution : MethodCitationCreatesExecution → ⊥
methodCitationDoesNotCreateExecution ()

institutionalFrameworkDoesNotCreateLocalAuthority :
  InstitutionalFrameworkCreatesLocalAuthority → ⊥
institutionalFrameworkDoesNotCreateLocalAuthority ()

------------------------------------------------------------------------
-- Canonical owners retained rather than copied.
------------------------------------------------------------------------

transformationBoundary = Transformation.canonicalIntegratedTransitionBoundary
literatureObserverMap = Literature.canonicalDigitalESDLiteratureMap
governanceTransferBoundary =
  Governance.canonicalParticipantGovernanceContextTransferBoundary
paymentBoundary = Payment.canonicalManuscriptDependencyPaymentBoundary
snowballBoundary = Snowball.canonicalAttributionSnowballBoundary

------------------------------------------------------------------------
-- Reporting boundary.
------------------------------------------------------------------------

record MethodologyBoundary : Set where
  constructor methodology-boundary
  field
    integrativeConceptualReviewDeclared : Bool
    integrativeConceptualReviewDeclaredIsTrue :
      integrativeConceptualReviewDeclared ≡ true
    transparentStructuredSearchRequired : Bool
    transparentStructuredSearchRequiredIsTrue :
      transparentStructuredSearchRequired ≡ true
    sourceRoleRetained : Bool
    sourceRoleRetainedIsTrue : sourceRoleRetained ≡ true
    sourcePopulationTimeScopeRetained : Bool
    sourcePopulationTimeScopeRetainedIsTrue :
      sourcePopulationTimeScopeRetained ≡ true
    lifecycleAndCircularityBoundariesRetained : Bool
    lifecycleAndCircularityBoundariesRetainedIsTrue :
      lifecycleAndCircularityBoundariesRetained ≡ true
    participantAuthorityBoundariesRetained : Bool
    participantAuthorityBoundariesRetainedIsTrue :
      participantAuthorityBoundariesRetained ≡ true
    searchClosureEqualsEvidenceSynthesis : Bool
    searchClosureEqualsEvidenceSynthesisIsFalse :
      searchClosureEqualsEvidenceSynthesis ≡ false
    sourceAcquisitionEqualsStudyInclusion : Bool
    sourceAcquisitionEqualsStudyInclusionIsFalse :
      sourceAcquisitionEqualsStudyInclusion ≡ false
    promotesSystematicReview : Bool
    promotesSystematicReviewIsFalse : promotesSystematicReview ≡ false
    methodSourcesCreateMethodExecution : Bool
    methodSourcesCreateMethodExecutionIsFalse :
      methodSourcesCreateMethodExecution ≡ false
    paperCreatesSameObjectEmpiricalEvidence : Bool
    paperCreatesSameObjectEmpiricalEvidenceIsFalse :
      paperCreatesSameObjectEmpiricalEvidence ≡ false

open MethodologyBoundary public

canonicalMethodologyBoundary : MethodologyBoundary
canonicalMethodologyBoundary =
  methodology-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

methodologyReading : String
methodologyReading =
  "This manuscript is an integrative conceptual review with a transparent structured search, not a systematic review and not an empirical intervention study. Search execution, eligibility, extraction and synthesis remain distinct receipts. Sources are extracted with role, population/context, time horizon, lifecycle/governance coordinates and explicit limitations. The reciprocal synthesis asks both how digital education can build ESD capacity and how sustainability should constrain digital education itself."
