module DASHI.Ontology.EducationViaOntologyExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Ontology.WikidataEpistemicBridge as Wikidata

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION BOUNDARY
--
-- Source:
--   Susanna Mkrtchyan,
--   "Education via Ontology engineering & Wikipedia",
--   Institute for Informatics and Automation Problems, Armenia.
--
-- The constructors below record what the supplied presentation states.
-- They are source claims, not empirical pedagogical theorems and not generic
-- claims about every LLM, Wikipedia deployment, Wikidata deployment, or
-- DBpedia deployment.
------------------------------------------------------------------------

data MkrtchyanSourceClaim : Set where
  ontologyPedagogicalInstrumentClaim : MkrtchyanSourceClaim
  ontologyTopDownLearningClaim : MkrtchyanSourceClaim
  ontologyBuildingAssignmentClaim : MkrtchyanSourceClaim
  wikipediaOntologyUmbrellaClaim : MkrtchyanSourceClaim
  flippedClassroomWorkflowClaim : MkrtchyanSourceClaim
  futureCohortReuseClaim : MkrtchyanSourceClaim
  languageDBpediaExtensionClaim : MkrtchyanSourceClaim
  aiOntologyReasoningClaim : MkrtchyanSourceClaim
  llmQueriesDBpediaClaim : MkrtchyanSourceClaim
  pedagogicalBenefitClaim : MkrtchyanSourceClaim

mkrtchyanSource : Transport.SourceBackedClaim
mkrtchyanSource = record
  { Transport.SourceClaim = MkrtchyanSourceClaim
  ; Transport.sourceReceipt = ontologyBuildingAssignmentClaim
  ; Transport.sourceName = "Susanna Mkrtchyan, Education via Ontology engineering & Wikipedia"
  ; Transport.sourceLocator = "Institute for Informatics and Automation Problems, Armenia; supplied 14-page presentation"
  ; Transport.reading = "bounded source attribution only; local DASHI reconstructions and empirical promotion require separate receipts"
  }

data SourceClaimAuthority : Set where
  sourceClaimOnly : SourceClaimAuthority

data SourceClaimPromotionPermission : SourceClaimAuthority → Set where

sourceClaimCannotPromoteItself :
  SourceClaimPromotionPermission sourceClaimOnly → ⊥
sourceClaimCannotPromoteItself ()

------------------------------------------------------------------------
-- COURSE ONTOLOGY: richer carrier, tree as a bounded presentation view.
--
-- The source presentation calls the Wikipedia-facing ontology a tree of
-- concept titles.  DASHI keeps the richer relation/provenance carrier distinct
-- and makes the title tree an explicit projection rather than redefining every
-- ontology as a tree.
------------------------------------------------------------------------

record CourseOntology : Set where
  constructor courseOntology
  field
    discipline : String
    modules : List String
    concepts : List String
    properties : List String
    relations : List String
    sourceReferences : List String
    revision : Nat

open CourseOntology public

record OntologyTreeView : Set where
  constructor ontologyTreeView
  field
    rootTitle : String
    conceptTitles : List String

open OntologyTreeView public

projectTree : CourseOntology → OntologyTreeView
projectTree o = ontologyTreeView (discipline o) (concepts o)

projectTreePreservesRoot :
  (o : CourseOntology) → rootTitle (projectTree o) ≡ discipline o
projectTreePreservesRoot o = refl

projectTreePreservesConceptTitles :
  (o : CourseOntology) → conceptTitles (projectTree o) ≡ concepts o
projectTreePreservesConceptTitles o = refl

------------------------------------------------------------------------
-- WIKIPEDIA STATUS / GAP NON-COLLAPSE
--
-- Source workflow:
--   blue = existing article;
--   red = missing/apparently missing article;
--   then verify whether the title exists under another title.
--
-- Therefore a red/title observation cannot be promoted directly to a missing
-- concept or missing item of knowledge.
------------------------------------------------------------------------

data ObservedArticleStatus : Set where
  existingBlue : ObservedArticleStatus
  apparentlyMissingRed : ObservedArticleStatus
  aliasUnresolved : ObservedArticleStatus

data GapKind : Set where
  noObservedGap : GapKind
  titleResolutionGap : GapKind
  articleGap : GapKind
  conceptGap : GapKind
  knowledgeGap : GapKind

observedGapKind : ObservedArticleStatus → GapKind
observedGapKind existingBlue = noObservedGap
observedGapKind apparentlyMissingRed = titleResolutionGap
observedGapKind aliasUnresolved = titleResolutionGap

titleGapNotArticleGap : titleResolutionGap ≡ articleGap → ⊥
titleGapNotArticleGap ()

titleGapNotConceptGap : titleResolutionGap ≡ conceptGap → ⊥
titleGapNotConceptGap ()

titleGapNotKnowledgeGap : titleResolutionGap ≡ knowledgeGap → ⊥
titleGapNotKnowledgeGap ()

articleGapNotConceptGap : articleGap ≡ conceptGap → ⊥
articleGapNotConceptGap ()

articleGapNotKnowledgeGap : articleGap ≡ knowledgeGap → ⊥
articleGapNotKnowledgeGap ()

conceptGapNotKnowledgeGap : conceptGap ≡ knowledgeGap → ⊥
conceptGapNotKnowledgeGap ()

------------------------------------------------------------------------
-- CONTRIBUTION / ADMISSION AUTHORITY
--
-- A student-created article is a contribution candidate.  It is not promoted
-- to ontology truth merely because it was assigned, written, or published.
-- This mirrors the existing Wikidata repair boundary, where a proposed repair
-- is explicitly review-only.
------------------------------------------------------------------------

record ContributionCandidate : Set where
  constructor contributionCandidate
  field
    learner : String
    targetConcept : String
    proposedTitle : String
    supportingSources : List String
    courseRevision : Nat

open ContributionCandidate public

data ContributionAuthority : Set where
  contributionForReview : ContributionAuthority
  reviewedContribution : ContributionAuthority

data OntologyTruthPermission : ContributionAuthority → Set where
  reviewedMayEnterAdmissionPipeline :
    OntologyTruthPermission reviewedContribution

candidateCannotAssertOntologyTruth :
  OntologyTruthPermission contributionForReview → ⊥
candidateCannotAssertOntologyTruth ()

existingWikidataRepairReviewAuthority : Repair.RepairProposalAuthority
existingWikidataRepairReviewAuthority = Repair.proposalForReviewOnly

------------------------------------------------------------------------
-- SOURCE ARTICLE OBSERVATIONS CAN BE EMBEDDED IN THE EXISTING WIKIDATA-LIKE
-- ENVELOPE WITHOUT TURNING RANK INTO TRUTH.
------------------------------------------------------------------------

data CourseQualifierAxis : Set where
  titleResolved : CourseQualifierAxis
  sourceReviewed : CourseQualifierAxis

courseStatementRankRemainsMetadata : Bool
courseStatementRankRemainsMetadata = Wikidata.rankIsTruthValue

courseStatementRankRemainsMetadataIsFalse :
  courseStatementRankRemainsMetadata ≡ false
courseStatementRankRemainsMetadataIsFalse = Wikidata.rankIsTruthValueIsFalse

------------------------------------------------------------------------
-- SOURCE METHODOLOGY AS A THREE-STAGE COURSE WORKFLOW.
------------------------------------------------------------------------

data CourseStage : Set where
  ontologyBuilding : CourseStage
  wikipediaContribution : CourseStage
  flippedClassroomPresentation : CourseStage

data StageStep : CourseStage → CourseStage → Set where
  ontologyToWikipedia : StageStep ontologyBuilding wikipediaContribution
  wikipediaToPresentation : StageStep wikipediaContribution flippedClassroomPresentation

------------------------------------------------------------------------
-- VERSIONED COHORT REFINEMENT.
--
-- The source proposes storing a completed ontology so future cohorts can
-- reuse, update, and expand it.  The revision carrier below makes that a
-- persistent transition with retained prior state, accepted changes,
-- residual gaps, and provenance.
------------------------------------------------------------------------

record CohortRevision : Set where
  constructor cohortRevision
  field
    priorOntology : CourseOntology
    acceptedConcepts : List String
    acceptedProperties : List String
    acceptedRelations : List String
    residualGaps : List GapKind
    revisionProvenance : List String

open CohortRevision public

nextOntology : CohortRevision → CourseOntology
nextOntology r =
  courseOntology
    (discipline (priorOntology r))
    (modules (priorOntology r))
    (acceptedConcepts r)
    (acceptedProperties r)
    (acceptedRelations r)
    (revisionProvenance r)
    (suc (revision (priorOntology r)))

nextOntologyPreservesDiscipline :
  (r : CohortRevision) →
  discipline (nextOntology r) ≡ discipline (priorOntology r)
nextOntologyPreservesDiscipline r = refl

nextOntologyAdvancesRevision :
  (r : CohortRevision) →
  revision (nextOntology r) ≡ suc (revision (priorOntology r))
nextOntologyAdvancesRevision r = refl

nextOntologyCarriesRevisionProvenance :
  (r : CohortRevision) →
  sourceReferences (nextOntology r) ≡ revisionProvenance r
nextOntologyCarriesRevisionProvenance r = refl

------------------------------------------------------------------------
-- PEDAGOGICAL / AI PROMOTION FIREWALLS.
--
-- The presentation reports pedagogical benefits and depicts an LLM/DBpedia
-- verification relation.  Neither is derived from the finite workflow above.
------------------------------------------------------------------------

data PedagogicalEfficacyPermission : Set where

data GenericLLMVerificationPermission : Set where

workflowDoesNotProvePedagogicalEfficacy : PedagogicalEfficacyPermission → ⊥
workflowDoesNotProvePedagogicalEfficacy ()

sourceDiagramDoesNotProveGenericLLMVerification :
  GenericLLMVerificationPermission → ⊥
sourceDiagramDoesNotProveGenericLLMVerification ()

------------------------------------------------------------------------
-- STATUS / ROADMAP RECEIPT
------------------------------------------------------------------------

record EducationViaOntologyStatus : Set where
  constructor educationViaOntologyStatus
  field
    sourceClaimsAreBounded : Bool
    ontologyTreeIsProjection : Bool
    gapKindsRemainDistinct : Bool
    contributionsRequireReview : Bool
    cohortRevisionPreservesProvenance : Bool
    pedagogicalEfficacyRequiresExternalEvidence : Bool
    genericLLMVerificationNotPromoted : Bool

    sourceClaimsAreBoundedIsTrue : sourceClaimsAreBounded ≡ true
    ontologyTreeIsProjectionIsTrue : ontologyTreeIsProjection ≡ true
    gapKindsRemainDistinctIsTrue : gapKindsRemainDistinct ≡ true
    contributionsRequireReviewIsTrue : contributionsRequireReview ≡ true
    cohortRevisionPreservesProvenanceIsTrue : cohortRevisionPreservesProvenance ≡ true
    pedagogicalEfficacyRequiresExternalEvidenceIsTrue :
      pedagogicalEfficacyRequiresExternalEvidence ≡ true
    genericLLMVerificationNotPromotedIsTrue :
      genericLLMVerificationNotPromoted ≡ true

open EducationViaOntologyStatus public

canonicalEducationViaOntologyStatus : EducationViaOntologyStatus
canonicalEducationViaOntologyStatus =
  educationViaOntologyStatus
    true true true true true true true
    refl refl refl refl refl refl refl
