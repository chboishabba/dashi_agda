module DASHI.Education.DigitalESDPaperTypeRequirementParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.RequirementProducerSchedulerExact as Scheduler
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition

------------------------------------------------------------------------
-- PAPER-TYPE / CONSUMER-RELATIVE REQUIREMENT SCHEDULER
--
-- The present design conversation supports an integrative conceptual review
-- with a transparent structured search. A systematic review and an empirical
-- intervention study are separate consumers with different obligations.
-- Nothing here upgrades the manuscript type merely because a method source is
-- cited. The exact search/database/screening/extraction receipts remain work
-- products of the human research team.
------------------------------------------------------------------------

whittemoreKnaflIntegrativeReviewSource : Attr.AttributedSource
whittemoreKnaflIntegrativeReviewSource =
  Attr.mkDOISource
    "Robin Whittemore; Kathleen Knafl"
    "The integrative review: updated methodology"
    "Journal of Advanced Nursing 52(5), 546-553"
    "2005"
    "10.1111/j.1365-2648.2005.03621.x"
    "https://doi.org/10.1111/j.1365-2648.2005.03621.x"
    Attr.academicArticleSource
    "Methodological source for integrative-review purpose specification, search, source evaluation, analysis/synthesis and presentation across diverse empirical/theoretical material; not an MDPI mandate and not proof that this manuscript has executed those steps."
    Attr.publicAttribution

sanraNarrativeReviewSource : Attr.AttributedSource
sanraNarrativeReviewSource =
  Attr.mkDOISource
    "Christopher Baethge; Sandra Goldbeck-Wood; Stephan Mertens"
    "SANRA-a scale for the quality assessment of narrative review articles"
    "Research Integrity and Peer Review 4, 5"
    "2019"
    "10.1186/s41073-019-0064-8"
    "https://doi.org/10.1186/s41073-019-0064-8"
    Attr.academicArticleSource
    "Quality-assessment source for non-systematic/narrative review importance, aims, search description, referencing, evidence level and endpoint data; developed in medical publishing and retained as a methodological comparator rather than a universal journal requirement."
    Attr.publicAttribution

prisma2020Source : Attr.AttributedSource
prisma2020Source =
  Attr.mkDOISource
    "Matthew J. Page et al."
    "The PRISMA 2020 statement: an updated guideline for reporting systematic reviews"
    "BMJ 372:n71"
    "2021"
    "10.1136/bmj.n71"
    "https://doi.org/10.1136/bmj.n71"
    Attr.academicArticleSource
    "Systematic-review reporting guideline covering identification, selection, appraisal and synthesis; primarily designed for systematic reviews and not automatically applicable to an integrative conceptual review."
    Attr.publicAttribution

paperMethodSourceAtlas : Attr.AttributedSourceAtlas
paperMethodSourceAtlas =
  Attr.mkSourceAtlas
    "digital ESD paper-type methodology sources"
    "DASHI.Education.DigitalESDPaperTypeRequirementParetoExact"
    ( whittemoreKnaflIntegrativeReviewSource
    ∷ sanraNarrativeReviewSource
    ∷ prisma2020Source
    ∷ []
    )
    "Method sources constrain review-type obligations only within their stated scope; citation creates neither completed protocol nor journal authority."

whittemoreSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt whittemoreKnaflIntegrativeReviewSource
whittemoreSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt whittemoreKnaflIntegrativeReviewSource

sanraSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt sanraNarrativeReviewSource
sanraSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt sanraNarrativeReviewSource

prismaSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt prisma2020Source
prismaSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt prisma2020Source

data PaperType : Set where
  integrativeConceptualReview : PaperType
  systematicReview : PaperType
  empiricalDigitalESDIntervention : PaperType

currentPaperType : PaperType
currentPaperType = integrativeConceptualReview

data ReviewCoordinate : Set where
  explicitPaperTypeDeclaration : ReviewCoordinate
  transparentStructuredSearch : ReviewCoordinate
  sourceRoleScopeSynthesis : ReviewCoordinate
  reciprocalFrameworkSynthesis : ReviewCoordinate
  lifecycleEvidenceSynthesis : ReviewCoordinate
  participantGovernanceEvidenceSynthesis : ReviewCoordinate
  longitudinalEvidenceSynthesis : ReviewCoordinate
  reproducibleSystematicProtocol : ReviewCoordinate
  screeningExtractionAuditTrail : ReviewCoordinate
  sameObjectInterventionLCA : ReviewCoordinate

data ReviewProducer : Set where
  paperTypeDeclarationProducer : ReviewProducer
  structuredSearchProducer : ReviewProducer
  sourceScopeMatrixProducer : ReviewProducer
  reciprocalFrameworkProducer : ReviewProducer
  lifecycleEvidenceProducer : ReviewProducer
  participantGovernanceProducer : ReviewProducer
  longitudinalEvidenceProducer : ReviewProducer
  systematicProtocolProducer : ReviewProducer
  screeningExtractionProducer : ReviewProducer
  interventionLCAProducer : ReviewProducer

requiredFor : PaperType → ReviewCoordinate → Bool
requiredFor integrativeConceptualReview explicitPaperTypeDeclaration = true
requiredFor integrativeConceptualReview transparentStructuredSearch = true
requiredFor integrativeConceptualReview sourceRoleScopeSynthesis = true
requiredFor integrativeConceptualReview reciprocalFrameworkSynthesis = true
requiredFor integrativeConceptualReview lifecycleEvidenceSynthesis = true
requiredFor integrativeConceptualReview participantGovernanceEvidenceSynthesis = true
requiredFor integrativeConceptualReview longitudinalEvidenceSynthesis = true
requiredFor integrativeConceptualReview reproducibleSystematicProtocol = false
requiredFor integrativeConceptualReview screeningExtractionAuditTrail = false
requiredFor integrativeConceptualReview sameObjectInterventionLCA = false

requiredFor systematicReview explicitPaperTypeDeclaration = true
requiredFor systematicReview transparentStructuredSearch = true
requiredFor systematicReview sourceRoleScopeSynthesis = true
requiredFor systematicReview reciprocalFrameworkSynthesis = true
requiredFor systematicReview lifecycleEvidenceSynthesis = true
requiredFor systematicReview participantGovernanceEvidenceSynthesis = true
requiredFor systematicReview longitudinalEvidenceSynthesis = true
requiredFor systematicReview reproducibleSystematicProtocol = true
requiredFor systematicReview screeningExtractionAuditTrail = true
requiredFor systematicReview sameObjectInterventionLCA = false

requiredFor empiricalDigitalESDIntervention explicitPaperTypeDeclaration = true
requiredFor empiricalDigitalESDIntervention transparentStructuredSearch = false
requiredFor empiricalDigitalESDIntervention sourceRoleScopeSynthesis = true
requiredFor empiricalDigitalESDIntervention reciprocalFrameworkSynthesis = true
requiredFor empiricalDigitalESDIntervention lifecycleEvidenceSynthesis = true
requiredFor empiricalDigitalESDIntervention participantGovernanceEvidenceSynthesis = true
requiredFor empiricalDigitalESDIntervention longitudinalEvidenceSynthesis = true
requiredFor empiricalDigitalESDIntervention reproducibleSystematicProtocol = false
requiredFor empiricalDigitalESDIntervention screeningExtractionAuditTrail = false
requiredFor empiricalDigitalESDIntervention sameObjectInterventionLCA = true

-- Closure is intentionally manuscript-work specific. Source acquisition can
-- make a coordinate cheaper without falsely claiming that the paper has
-- executed its search/synthesis/reporting work.
closed : ReviewCoordinate → Bool
closed explicitPaperTypeDeclaration = true
closed reciprocalFrameworkSynthesis = true
closed _ = false

producerFor : ReviewCoordinate → ReviewProducer
producerFor explicitPaperTypeDeclaration = paperTypeDeclarationProducer
producerFor transparentStructuredSearch = structuredSearchProducer
producerFor sourceRoleScopeSynthesis = sourceScopeMatrixProducer
producerFor reciprocalFrameworkSynthesis = reciprocalFrameworkProducer
producerFor lifecycleEvidenceSynthesis = lifecycleEvidenceProducer
producerFor participantGovernanceEvidenceSynthesis = participantGovernanceProducer
producerFor longitudinalEvidenceSynthesis = longitudinalEvidenceProducer
producerFor reproducibleSystematicProtocol = systematicProtocolProducer
producerFor screeningExtractionAuditTrail = screeningExtractionProducer
producerFor sameObjectInterventionLCA = interventionLCAProducer

digitalESDPaperRequirementSystem : Scheduler.RequirementSystem
digitalESDPaperRequirementSystem =
  Scheduler.requirement-system
    PaperType
    ReviewCoordinate
    ReviewProducer
    requiredFor
    closed
    producerFor
    "consumer-relative digital-ESD manuscript requirements"
    "paper-type declaration, structured search, source/scope synthesis, reciprocal framework, evidence syntheses, systematic protocol/screening when applicable, and same-object LCA only for an empirical intervention consumer"

currentMissingStructuredSearch :
  Scheduler.MissingFor
    digitalESDPaperRequirementSystem
    integrativeConceptualReview
    transparentStructuredSearch
currentMissingStructuredSearch = refl , refl

currentStructuredSearchProducer : ReviewProducer
currentStructuredSearchProducer =
  Scheduler.scheduledProducer
    (Scheduler.missing-coordinate-receipt
      {sys = digitalESDPaperRequirementSystem}
      {q = integrativeConceptualReview}
      transparentStructuredSearch currentMissingStructuredSearch)

currentStructuredSearchProducerIsCorrect :
  currentStructuredSearchProducer ≡ structuredSearchProducer
currentStructuredSearchProducerIsCorrect = refl

------------------------------------------------------------------------
-- Review-method non-promotion boundaries.
------------------------------------------------------------------------

data SystematicReviewLabelWithoutProtocol : Set where

data ConceptualReviewRequiresSameObjectInterventionLCA : Set where

data MethodCitationClosesMethodExecution : Set where

data PRISMAAutomaticallyAppliesToConceptualReview : Set where

systematicReviewLabelRequiresProtocol :
  SystematicReviewLabelWithoutProtocol → ⊥
systematicReviewLabelRequiresProtocol ()

conceptualReviewDoesNotRequireSameObjectInterventionLCA :
  ConceptualReviewRequiresSameObjectInterventionLCA → ⊥
conceptualReviewDoesNotRequireSameObjectInterventionLCA ()

methodCitationDoesNotCloseExecution : MethodCitationClosesMethodExecution → ⊥
methodCitationDoesNotCloseExecution ()

prismaDoesNotAutomaticallyApplyToConceptualReview :
  PRISMAAutomaticallyAppliesToConceptualReview → ⊥
prismaDoesNotAutomaticallyApplyToConceptualReview ()

------------------------------------------------------------------------
-- Current conceptual-review frontier. Acquisition debt and manuscript-work
-- debt are different fibres: the source atlas can be rich while synthesis and
-- transparent search are still unfinished.
------------------------------------------------------------------------

currentConceptualReviewFrontier : List ReviewCoordinate
currentConceptualReviewFrontier =
  transparentStructuredSearch
  ∷ sourceRoleScopeSynthesis
  ∷ lifecycleEvidenceSynthesis
  ∷ participantGovernanceEvidenceSynthesis
  ∷ longitudinalEvidenceSynthesis
  ∷ []

currentFirstPaperProducer : ReviewProducer
currentFirstPaperProducer = structuredSearchProducer

sameObjectLifecycleReopensForEmpiricalConsumer :
  requiredFor empiricalDigitalESDIntervention sameObjectInterventionLCA ≡ true
sameObjectLifecycleReopensForEmpiricalConsumer = refl

sameObjectLifecycleNotCurrentConceptualRequirement :
  requiredFor integrativeConceptualReview sameObjectInterventionLCA ≡ false
sameObjectLifecycleNotCurrentConceptualRequirement = refl

acquisitionContextRetained : Acquisition.DigitalESDAcquisitionAtlas
acquisitionContextRetained = Acquisition.canonicalDigitalESDAcquisitionAtlas
