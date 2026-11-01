module DASHI.Education.DigitalESDStructuredSearchExact where

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

------------------------------------------------------------------------
-- TRANSPARENT STRUCTURED-SEARCH LEDGER
--
-- This is an execution-status ledger for the current integrative conceptual
-- review. It records searches actually observed in this research session and
-- separately records bibliographic surfaces that remain planned/unobserved.
--
-- It does NOT:
--   * call the manuscript a systematic review;
--   * invent Scopus/WoS/ERIC/ACM/IEEE execution receipts;
--   * treat an open-web snowball as an exhaustive literature search;
--   * let method citations stand in for method execution.
------------------------------------------------------------------------

prismaSSource : Attr.AttributedSource
prismaSSource =
  Attr.mkDOISource
    "Melissa L. Rethlefsen; Shona Kirtley; Siw Waffenschmidt; Ana Patricia Ayala; David Moher; Matthew J. Page; Jonathan B. Koffel; PRISMA-S Group"
    "PRISMA-S: an extension to the PRISMA Statement for Reporting Literature Searches in Systematic Reviews"
    "Systematic Reviews 10, 39"
    "2021"
    "10.1186/s13643-020-01542-z"
    "https://doi.org/10.1186/s13643-020-01542-z"
    Attr.academicArticleSource
    "Search-reporting methodology source for clear/reproducible reporting of information sources and search methods. Retained as a methodological comparator for this integrative review; citation does not create systematic-review status or prove execution."
    Attr.publicAttribution

press2015Source : Attr.AttributedSource
press2015Source =
  Attr.mkDOISource
    "Jessie McGowan; Margaret Sampson; Douglas M. Salzwedel; Elise Cogo; Vicki Foerster; Carol Lefebvre"
    "PRESS Peer Review of Electronic Search Strategies: 2015 Guideline Statement"
    "Journal of Clinical Epidemiology 75, 40-46"
    "2016"
    "10.1016/j.jclinepi.2016.01.021"
    "https://doi.org/10.1016/j.jclinepi.2016.01.021"
    Attr.academicArticleSource
    "Electronic-search strategy quality source covering research-question translation, Boolean/proximity operators, subject headings, text words, syntax and limits/filters. It can calibrate a search design but does not prove this search was peer-reviewed or executed."
    Attr.publicAttribution

structuredSearchMethodAtlas : Attr.AttributedSourceAtlas
structuredSearchMethodAtlas =
  Attr.mkSourceAtlas
    "digital ESD structured-search method sources"
    "DASHI.Education.DigitalESDStructuredSearchExact"
    (prismaSSource ∷ press2015Source ∷ [])
    "Method sources for transparent search reporting and search-strategy quality; neither citation nor atlas membership promotes systematic-review status, completeness, peer review, or execution."

prismaSSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt prismaSSource
prismaSSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt prismaSSource

pressSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt press2015Source
pressSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt press2015Source

------------------------------------------------------------------------
-- Search question families. They are deliberately orthogonal enough that a
-- result about "technology for ESD" cannot silently pay "sustainability of
-- technology" or lifecycle/agency/durability claims.
------------------------------------------------------------------------

data SearchQueryFamily : Set where
  digitalEducationESD : SearchQueryFamily
  reflexiveDigitalSustainability : SearchQueryFamily
  lifecycleCircularity : SearchQueryFamily
  participantAgencyGovernance : SearchQueryFamily
  longitudinalInstitutionalImpact : SearchQueryFamily
  openInteroperabilityRepairability : SearchQueryFamily

canonicalSearchQueryFamilies : List SearchQueryFamily
canonicalSearchQueryFamilies =
  digitalEducationESD
  ∷ reflexiveDigitalSustainability
  ∷ lifecycleCircularity
  ∷ participantAgencyGovernance
  ∷ longitudinalInstitutionalImpact
  ∷ openInteroperabilityRepairability
  ∷ []

queryFamilyReference : SearchQueryFamily → String
queryFamilyReference digitalEducationESD =
  "digital innovation / online education / digital education × ESD / sustainability / sustainable development"
queryFamilyReference reflexiveDigitalSustainability =
  "digital technology as sustainability object × environmental/social/economic impact × digital sobriety / critical ESD"
queryFamilyReference lifecycleCircularity =
  "education technology / ICT / AI × life cycle assessment / energy / carbon / water / e-waste / circularity"
queryFamilyReference participantAgencyGovernance =
  "ESD / digital education × student voice / learner agency / participatory research / co-design / governance"
queryFamilyReference longitudinalInstitutionalImpact =
  "digital ESD / sustainable education × longitudinal / institutionalisation / durability / long-term impact"
queryFamilyReference openInteroperabilityRepairability =
  "digital learning / education technology × open standards / OER / interoperability / vendor lock-in / repairability / right to repair"

data SearchSurface : Set where
  openWebSearch : SearchSurface
  scopus : SearchSurface
  webOfScience : SearchSurface
  eric : SearchSurface
  acmDigitalLibrary : SearchSurface
  ieeeXplore : SearchSurface

record ObservedSearchReceipt : Set where
  constructor observed-search-receipt
  field
    surface : SearchSurface
    family : SearchQueryFamily
    executedQueryReference : String
    acquiredOn : String
    observationScope : String

open ObservedSearchReceipt public

observedDigitalEducationESDSearch : ObservedSearchReceipt
observedDigitalEducationESDSearch =
  observed-search-receipt
    openWebSearch
    digitalEducationESD
    "digital education environmental impact systematic review higher education ICT lifecycle sustainability education carbon footprint"
    "2026-09-16"
    "open-web research acquisition; discovery/snowball evidence, not database-complete review execution"

observedReflexiveSustainabilitySearch : ObservedSearchReceipt
observedReflexiveSustainabilitySearch =
  observed-search-receipt
    openWebSearch
    reflexiveDigitalSustainability
    "digital sustainability education lifecycle assessment ICT education systematic review 2024 2025 2026"
    "2026-09-16"
    "open-web research acquisition; identified reflexive-sustainability and digital-sobriety literature"

observedLifecycleCircularitySearch : ObservedSearchReceipt
observedLifecycleCircularitySearch =
  observed-search-receipt
    openWebSearch
    lifecycleCircularity
    "ITU-T L.1410 ICT LCA; ITU-T L.1023 circularity performance; education LCA; data-centre energy; e-waste"
    "2026-09-16"
    "primary-standard and literature snowball; source identities/method roles observed, deployment measurements still separate"

observedParticipantGovernanceSearch : ObservedSearchReceipt
observedParticipantGovernanceSearch =
  observed-search-receipt
    openWebSearch
    participantAgencyGovernance
    "education for sustainable development participatory research student voice co-design learner agency systematic review"
    "2026-09-16"
    "open-web snowball into participatory-ESD literature; does not transfer Alice Brown authority stages automatically"

observedLongitudinalImpactSearch : ObservedSearchReceipt
observedLongitudinalImpactSearch =
  observed-search-receipt
    openWebSearch
    longitudinalInstitutionalImpact
    "education for sustainable development longitudinal intervention long-term impact institutional sustainability digital education"
    "2026-09-16"
    "open-web snowball into longitudinal ESD evidence; not a completed longitudinal digital-ESD synthesis"

observedOpenDurabilitySearch : ObservedSearchReceipt
observedOpenDurabilitySearch =
  observed-search-receipt
    openWebSearch
    openInteroperabilityRepairability
    "public digital learning platforms open standards interoperability vendor lock-in education right to repair OER sustainability"
    "2026-09-16"
    "open-web and primary institutional snowball; normative/practice sources do not prove deployed durability"

canonicalObservedOpenWebSearches : List ObservedSearchReceipt
canonicalObservedOpenWebSearches =
  observedDigitalEducationESDSearch
  ∷ observedReflexiveSustainabilitySearch
  ∷ observedLifecycleCircularitySearch
  ∷ observedParticipantGovernanceSearch
  ∷ observedLongitudinalImpactSearch
  ∷ observedOpenDurabilitySearch
  ∷ []

------------------------------------------------------------------------
-- Execution status. Planned databases are not execution receipts.
------------------------------------------------------------------------

record StructuredSearchLedger : Set where
  constructor structured-search-ledger
  field
    methodSources : Attr.AttributedSourceAtlas
    queryFamilies : List SearchQueryFamily
    observedOpenWebSearches : List ObservedSearchReceipt

    openWebSnowballObserved : Bool
    openWebSnowballObservedIsTrue : openWebSnowballObserved ≡ true

    scopusExecutionObserved : Bool
    scopusExecutionObservedIsFalse : scopusExecutionObserved ≡ false
    webOfScienceExecutionObserved : Bool
    webOfScienceExecutionObservedIsFalse : webOfScienceExecutionObserved ≡ false
    ericExecutionObserved : Bool
    ericExecutionObservedIsFalse : ericExecutionObserved ≡ false
    acmDigitalLibraryExecutionObserved : Bool
    acmDigitalLibraryExecutionObservedIsFalse :
      acmDigitalLibraryExecutionObserved ≡ false
    ieeeXploreExecutionObserved : Bool
    ieeeXploreExecutionObservedIsFalse : ieeeXploreExecutionObserved ≡ false

    databaseDeduplicationObserved : Bool
    databaseDeduplicationObservedIsFalse :
      databaseDeduplicationObserved ≡ false
    eligibilityScreeningObserved : Bool
    eligibilityScreeningObservedIsFalse : eligibilityScreeningObserved ≡ false
    structuredExtractionObserved : Bool
    structuredExtractionObservedIsFalse : structuredExtractionObserved ≡ false
    transparentStructuredSearchClosed : Bool
    transparentStructuredSearchClosedIsFalse :
      transparentStructuredSearchClosed ≡ false

    citationCreatesExecutionReceipt : Bool
    citationCreatesExecutionReceiptIsFalse : citationCreatesExecutionReceipt ≡ false
    openWebSnowballEqualsSystematicSearch : Bool
    openWebSnowballEqualsSystematicSearchIsFalse :
      openWebSnowballEqualsSystematicSearch ≡ false

open StructuredSearchLedger public

canonicalStructuredSearchLedger : StructuredSearchLedger
canonicalStructuredSearchLedger =
  structured-search-ledger
    structuredSearchMethodAtlas
    canonicalSearchQueryFamilies
    canonicalObservedOpenWebSearches
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- No-promotion / execution boundaries.
------------------------------------------------------------------------

data OpenWebSnowballClosesTransparentStructuredSearch : Set where

data SearchMethodCitationPromotesSystematicReview : Set where

data PlannedDatabaseCreatesExecutionReceipt : Set where

data SearchHitCreatesIncludedStudy : Set where

data SearchResultSnippetPaysFullSourceClaim : Set where

data UnobservedDatabaseClosesStructuredSearch : Set where

data StructuredSearchClosurePaysEvidenceSynthesis : Set where

openWebSnowballDoesNotCloseTransparentStructuredSearch :
  OpenWebSnowballClosesTransparentStructuredSearch → ⊥
openWebSnowballDoesNotCloseTransparentStructuredSearch ()

searchMethodCitationDoesNotPromoteSystematicReview :
  SearchMethodCitationPromotesSystematicReview → ⊥
searchMethodCitationDoesNotPromoteSystematicReview ()

plannedDatabaseDoesNotCreateExecutionReceipt :
  PlannedDatabaseCreatesExecutionReceipt → ⊥
plannedDatabaseDoesNotCreateExecutionReceipt ()

searchHitDoesNotCreateIncludedStudy : SearchHitCreatesIncludedStudy → ⊥
searchHitDoesNotCreateIncludedStudy ()

searchResultSnippetDoesNotPayFullSourceClaim :
  SearchResultSnippetPaysFullSourceClaim → ⊥
searchResultSnippetDoesNotPayFullSourceClaim ()

unobservedDatabaseDoesNotCloseStructuredSearch :
  UnobservedDatabaseClosesStructuredSearch → ⊥
unobservedDatabaseDoesNotCloseStructuredSearch ()

structuredSearchClosureDoesNotPayEvidenceSynthesis :
  StructuredSearchClosurePaysEvidenceSynthesis → ⊥
structuredSearchClosureDoesNotPayEvidenceSynthesis ()

------------------------------------------------------------------------
-- Executable search lineage. These types describe the evidence that future
-- search execution must return; they do not create any canonical database
-- receipt for searches that have not been observed.
------------------------------------------------------------------------

record DatabaseExecutionReceipt (searchSurface : SearchSurface) : Set where
  constructor database-execution-receipt
  field
    executedFamilies : List SearchQueryFamily
    executedQueryReference : String
    executionDate : String
    resultExportReference : String
    resultCount : Nat

    executionObserved : Bool
    executionObservedIsTrue : executionObserved ≡ true

    queryReferenceRetained : Bool
    queryReferenceRetainedIsTrue : queryReferenceRetained ≡ true

    resultExportRetained : Bool
    resultExportRetainedIsTrue : resultExportRetained ≡ true

    sourceRoleRetained : Bool
    sourceRoleRetainedIsTrue : sourceRoleRetained ≡ true

open DatabaseExecutionReceipt public

record DeduplicationReceipt
    (scopusReceipt : DatabaseExecutionReceipt scopus)
    (wosReceipt : DatabaseExecutionReceipt webOfScience)
    (ericReceipt : DatabaseExecutionReceipt eric)
    (acmReceipt : DatabaseExecutionReceipt acmDigitalLibrary)
    (ieeeReceipt : DatabaseExecutionReceipt ieeeXplore) : Set where
  constructor deduplication-receipt
  field
    inputSetReference : String
    deduplicatedSetReference : String
    duplicateCount : Nat
    upstreamExportsRetained : Bool
    upstreamExportsRetainedIsTrue : upstreamExportsRetained ≡ true

open DeduplicationReceipt public

record EligibilityScreeningReceipt
    {scopusReceipt : DatabaseExecutionReceipt scopus}
    {wosReceipt : DatabaseExecutionReceipt webOfScience}
    {ericReceipt : DatabaseExecutionReceipt eric}
    {acmReceipt : DatabaseExecutionReceipt acmDigitalLibrary}
    {ieeeReceipt : DatabaseExecutionReceipt ieeeXplore}
    (dedup : DeduplicationReceipt
      scopusReceipt wosReceipt ericReceipt acmReceipt ieeeReceipt) : Set where
  constructor eligibility-screening-receipt
  field
    eligibilityCriteriaReference : String
    screenedSetReference : String
    includedSetReference : String
    excludedSetReference : String
    exclusionReasonLedgerReference : String
    deduplicatedInputRetained : Bool
    deduplicatedInputRetainedIsTrue : deduplicatedInputRetained ≡ true

open EligibilityScreeningReceipt public

record StructuredExtractionReceipt
    {scopusReceipt : DatabaseExecutionReceipt scopus}
    {wosReceipt : DatabaseExecutionReceipt webOfScience}
    {ericReceipt : DatabaseExecutionReceipt eric}
    {acmReceipt : DatabaseExecutionReceipt acmDigitalLibrary}
    {ieeeReceipt : DatabaseExecutionReceipt ieeeXplore}
    {dedup : DeduplicationReceipt
      scopusReceipt wosReceipt ericReceipt acmReceipt ieeeReceipt}
    (screening : EligibilityScreeningReceipt dedup) : Set where
  constructor structured-extraction-receipt
  field
    extractionSchemaReference : String
    extractedDatasetReference : String
    sourceRoleScopeMatrixReference : String
    includedSetRetained : Bool
    includedSetRetainedIsTrue : includedSetRetained ≡ true
    sourceRoleAndScopeRetained : Bool
    sourceRoleAndScopeRetainedIsTrue : sourceRoleAndScopeRetained ≡ true

open StructuredExtractionReceipt public

record TransparentStructuredSearchClosureReceipt : Set where
  constructor transparent-structured-search-closure-receipt
  field
    scopusReceipt : DatabaseExecutionReceipt scopus
    wosReceipt : DatabaseExecutionReceipt webOfScience
    ericReceipt : DatabaseExecutionReceipt eric
    acmReceipt : DatabaseExecutionReceipt acmDigitalLibrary
    ieeeReceipt : DatabaseExecutionReceipt ieeeXplore
    deduplicationReceipt : DeduplicationReceipt
      scopusReceipt wosReceipt ericReceipt acmReceipt ieeeReceipt
    screeningReceipt : EligibilityScreeningReceipt deduplicationReceipt
    extractionReceipt : StructuredExtractionReceipt screeningReceipt

    promotesSystematicReview : Bool
    promotesSystematicReviewIsFalse : promotesSystematicReview ≡ false

    closesEvidenceSynthesisCoordinates : Bool
    closesEvidenceSynthesisCoordinatesIsFalse :
      closesEvidenceSynthesisCoordinates ≡ false

    sourceRoleAndExecutionLineageRetained : Bool
    sourceRoleAndExecutionLineageRetainedIsTrue :
      sourceRoleAndExecutionLineageRetained ≡ true

open TransparentStructuredSearchClosureReceipt public

closeTransparentStructuredSearch :
  (scopusReceipt : DatabaseExecutionReceipt scopus) →
  (wosReceipt : DatabaseExecutionReceipt webOfScience) →
  (ericReceipt : DatabaseExecutionReceipt eric) →
  (acmReceipt : DatabaseExecutionReceipt acmDigitalLibrary) →
  (ieeeReceipt : DatabaseExecutionReceipt ieeeXplore) →
  (dedup : DeduplicationReceipt
    scopusReceipt wosReceipt ericReceipt acmReceipt ieeeReceipt) →
  (screening : EligibilityScreeningReceipt dedup) →
  (extraction : StructuredExtractionReceipt screening) →
  TransparentStructuredSearchClosureReceipt
closeTransparentStructuredSearch
    scopusReceipt wosReceipt ericReceipt acmReceipt ieeeReceipt
    dedup screening extraction =
  transparent-structured-search-closure-receipt
    scopusReceipt wosReceipt ericReceipt acmReceipt ieeeReceipt
    dedup screening extraction
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Consumer-relative connection back to the paper scheduler.
------------------------------------------------------------------------

paperStillRequiresTransparentStructuredSearch :
  Paper.requiredFor
    Paper.integrativeConceptualReview
    Paper.transparentStructuredSearch
  ≡ true
paperStillRequiresTransparentStructuredSearch = refl

paperTransparentStructuredSearchStillOpen :
  Paper.closed Paper.transparentStructuredSearch ≡ false
paperTransparentStructuredSearchStillOpen = refl

currentSearchStatusReading : String
currentSearchStatusReading =
  "Six query families have open-web snowball execution receipts dated 2026-09-16. Scopus, Web of Science, ERIC, ACM Digital Library and IEEE Xplore execution; database deduplication; eligibility screening; and structured extraction remain unobserved. The current manuscript therefore has a populated acquisition snowball but its transparent structured-search work coordinate remains open. The closure type now requires same-object database execution exports followed by dependent deduplication, screening and extraction receipts; no canonical instance is manufactured until those work products exist."
