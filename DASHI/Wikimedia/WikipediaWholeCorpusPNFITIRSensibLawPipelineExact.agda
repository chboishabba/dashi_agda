module DASHI.Wikimedia.WikipediaWholeCorpusPNFITIRSensibLawPipelineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SourceProvenanceExact as Source
import DASHI.Wikimedia.SensibLawWikipediaIngestContractExact as WikiIngest
import DASHI.Wikimedia.WikidataPNFPredicateBridgeExact as WDPredicate
import DASHI.Wikimedia.PredicateNormalFormWikipediaQidBridgeExact as PNFIdentity
import DASHI.Reasoning.SensibLawEncyclopediaCorpusClaimReceiptExact as Encyclopedia
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF
import DASHI.Cognition.PNF.EventAlgebra as EventPNF
import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIR

------------------------------------------------------------------------
-- SYSTEMATIC WHOLE-WIKIPEDIA -> ITIR / PNF / SENSIBLAW / WIKIDATA PIPELINE
--
-- Goal:
--   take a bounded Wikipedia snapshot/revision set;
--   preserve exact source/revision/span identity;
--   extract candidate assertions and objects;
--   compile candidates to evidence-bearing Predicate Normal Form;
--   resolve/link entities and predicates against Wikidata;
--   run typed PNF/SensibLaw algebra over relevant neighborhoods;
--   emit reviewable gaps, joins, contradictions, ambiguity and source debt.
--
-- This is a scheduler/receipt spine over existing owners, not a new parser.
-- It deliberately does not claim that the whole English Wikipedia has already
-- been acquired, parsed, resolved, logically checked or proved.
------------------------------------------------------------------------

data PipelineStage : Set where
  snapshotStage : PipelineStage
  shardStage : PipelineStage
  parseStage : PipelineStage
  passageStage : PipelineStage
  candidateClaimStage : PipelineStage
  predicateNormalFormStage : PipelineStage
  entityResolutionStage : PipelineStage
  wikidataAlignmentStage : PipelineStage
  sourceDiligenceStage : PipelineStage
  algebraStage : PipelineStage
  gapJoinStage : PipelineStage
  reviewStage : PipelineStage

record WikipediaSnapshotManifest : Set where
  constructor wikipedia-snapshot-manifest
  field
    corpusReference : String
    languageEdition : String
    snapshotReference : String
    snapshotDate : String
    sourceManifestReference : String
    sourceManifestHash : String
    namespacePolicyReference : String
    redirectPolicyReference : String
    revisionPolicyReference : String
open WikipediaSnapshotManifest public

record WikipediaArticleWorkItem : Set where
  constructor wikipedia-article-work-item
  field
    snapshot : WikipediaSnapshotManifest
    sourceRevision : Source.WikipediaRevisionReceipt
    parsedCarrier : WikiIngest.ParsedWikipediaCarrier
    parseReceipt : WikiIngest.ParseReceipt
    wikidataSubjectReference : String
    wikidataResolutionReference : String
open WikipediaArticleWorkItem public

record ArticlePassageWorkItem : Set where
  constructor article-passage-work-item
  field
    article : WikipediaArticleWorkItem
    passage : Encyclopedia.ExactPassageCarrier
    extraction : Encyclopedia.EncyclopediaExtractionReceipt
    sectionReference : String
    sentenceReference : String
    citationClusterReference : String
open ArticlePassageWorkItem public

record CandidateAssertionWorkItem : Set where
  constructor candidate-assertion-work-item
  field
    passage : ArticlePassageWorkItem
    propositionReference : String
    subjectCandidateReference : String
    predicateCandidateReference : String
    objectCandidateReference : String
    qualifierCandidateReference : String
    temporalCandidateReference : String
    modalityCandidateReference : String
    evidenceCandidateReference : String
    candidatePNFReference : String
    ambiguityLedgerReference : String
open CandidateAssertionWorkItem public

------------------------------------------------------------------------
-- Compilation and alignment remain separate payments.
------------------------------------------------------------------------

record PNFCompilationReceipt : Set where
  constructor pnf-compilation-receipt
  field
    candidate : CandidateAssertionWorkItem
    evidencePNFReference : String
    eventPNFReference : String
    parserObservationReference : String
    logicalCompilationReference : String
    alternativesRetained : Bool
    extractionCreatesWorldTruth : Bool
open PNFCompilationReceipt public

record WikidataAlignmentReceipt : Set where
  constructor wikidata-alignment-receipt
  field
    compiledClaim : PNFCompilationReceipt
    subjectQidReference : String
    predicatePropertyReference : String
    objectQidOrValueReference : String
    propertyPredicateAlignmentReference : String
    statementReference : String
    statementSourceReference : String
    alignmentStatusReference : String
    qidIdentityCreatesClaimTruth : Bool
open WikidataAlignmentReceipt public

record SourceDiligenceReceipt : Set where
  constructor source-diligence-receipt
  field
    alignedClaim : WikidataAlignmentReceipt
    wikipediaCitationReference : String
    citedSourceCanonicalReference : String
    citedSourceIdentityReference : String
    citedSourceInspectionReference : String
    sourceRoleReference : String
    sourceSupportsExactPropositionReference : String
    unresolvedSourceDebtReference : String
    sourceDiscoveryCreatesSupport : Bool
open SourceDiligenceReceipt public

------------------------------------------------------------------------
-- Algebra should be neighborhood-indexed, not global quadratic comparison.
------------------------------------------------------------------------

data NeighborhoodAxis : Set where
  sameSubjectQid : NeighborhoodAxis
  samePredicateProperty : NeighborhoodAxis
  sameObjectQid : NeighborhoodAxis
  sameCitationSource : NeighborhoodAxis
  wikipediaLinkNeighbor : NeighborhoodAxis
  wikidataGraphNeighbor : NeighborhoodAxis
  temporalOverlap : NeighborhoodAxis
  explicitContradictionCandidate : NeighborhoodAxis
  userSelectedDomain : NeighborhoodAxis

record IndexedClaim : Set where
  constructor indexed-claim
  field
    claimReference : String
    subjectIndex : String
    predicateIndex : String
    objectIndex : String
    sourceIndex : String
    revisionIndex : String
    temporalIndex : String
open IndexedClaim public

record NeighborhoodWorkUnit : Set where
  constructor neighborhood-work-unit
  field
    anchorClaim : IndexedClaim
    comparisonClaim : IndexedClaim
    selectionAxis : NeighborhoodAxis
    selectionReceipt : String
    sameClaimComparisonExcluded : Bool
open NeighborhoodWorkUnit public

data AlgebraFindingKind : Set where
  exactAgreement : AlgebraFindingKind
  compatibleQualification : AlgebraFindingKind
  partialResidual : AlgebraFindingKind
  contradiction : AlgebraFindingKind
  noTypedMeet : AlgebraFindingKind
  temporalDrift : AlgebraFindingKind
  sourceRoleMismatch : AlgebraFindingKind
  ontologyGap : AlgebraFindingKind
  ontologyJoinCandidate : AlgebraFindingKind
  missingWikidataStatement : AlgebraFindingKind
  missingWikipediaSupport : AlgebraFindingKind
  unresolvedEntityIdentity : AlgebraFindingKind
  unresolvedPredicateRole : AlgebraFindingKind
  biasInspectionCandidate : AlgebraFindingKind
  mathVerificationCandidate : AlgebraFindingKind

record AlgebraFinding : Set where
  constructor algebra-finding
  field
    workUnit : NeighborhoodWorkUnit
    findingKind : AlgebraFindingKind
    pnfComparisonReference : String
    residualReference : String
    sensibLawReference : String
    sourceDiligenceReference : String
    findingEvidenceReference : String
    autoPromotionAllowed : Bool
open AlgebraFinding public

------------------------------------------------------------------------
-- ITIR normalization: findings are reviewable claims / unresolved pressure,
-- not automatically promoted records.
------------------------------------------------------------------------

record ITIRFindingProjection : Set₁ where
  constructor itir-finding-projection
  field
    finding : AlgebraFinding
    sourceArtifact : ITIR.NormalizedArtifact
    provenanceAnchor : ITIR.NormalizedArtifact
    reviewableClaim : ITIR.NormalizedArtifact
    unresolvedPressure : ITIR.NormalizedArtifact
    sourceConceptExact : ITIR.concept sourceArtifact ≡ ITIR.sourceArtifact
    provenanceConceptExact : ITIR.concept provenanceAnchor ≡ ITIR.provenanceAnchor
    reviewConceptExact : ITIR.concept reviewableClaim ≡ ITIR.reviewableClaim
    pressureConceptExact :
      ITIR.concept unresolvedPressure ≡ ITIR.abstentionHoldUnresolvedPressure
open ITIRFindingProjection public

------------------------------------------------------------------------
-- Shard-level and corpus-level receipts.
------------------------------------------------------------------------

record WikipediaShardRunReceipt : Set where
  constructor wikipedia-shard-run-receipt
  field
    shard : WikiIngest.CorpusShard
    snapshotReference : String
    articleManifestReference : String
    parseManifestReference : String
    claimManifestReference : String
    pnfManifestReference : String
    wikidataAlignmentManifestReference : String
    sourceDiligenceManifestReference : String
    algebraFindingManifestReference : String
    reviewQueueManifestReference : String
    allOutputsRevisionBound : Bool
    allOutputsSourceBound : Bool
open WikipediaShardRunReceipt public

record WikipediaCorpusRunReceipt : Set where
  constructor wikipedia-corpus-run-receipt
  field
    snapshot : WikipediaSnapshotManifest
    shardManifestReference : String
    shardReceiptsReference : String
    qidIndexReference : String
    propertyIndexReference : String
    sourceIndexReference : String
    revisionIndexReference : String
    linkGraphIndexReference : String
    contradictionQueueReference : String
    gapJoinQueueReference : String
    biasInspectionQueueReference : String
    mathVerificationQueueReference : String
    unresolvedQueueReference : String
    everyScheduledShardHasReceipt : Bool
    wholeCorpusCoverageClaimed : Bool
open WikipediaCorpusRunReceipt public

------------------------------------------------------------------------
-- Operational plan: exact sequence to run at scale.
------------------------------------------------------------------------

record WholeWikipediaExecutionPlan : Set where
  constructor whole-wikipedia-execution-plan
  field
    acquireBoundedSnapshot : Bool
    buildRevisionManifest : Bool
    shardByStablePageIdentity : Bool
    parseWithPinnedSensibLawRevision : Bool
    hashParsedOutputs : Bool
    extractExactPassageClaims : Bool
    compileCandidatePredicateNormalForm : Bool
    retainAmbiguousAlternatives : Bool
    resolveQidsAndProperties : Bool
    inspectWikidataStatementSources : Bool
    inspectWikipediaCitedSources : Bool
    buildTypedIndices : Bool
    compareOnlyIndexedNeighborhoodsByDefault : Bool
    runPNFResidualAlgebra : Bool
    projectFindingsIntoITIR : Bool
    emitHumanReviewQueues : Bool
    incrementalRerunOnlyChangedRevisions : Bool
    naiveGlobalPairwiseComparison : Bool
    parserOutputCreatesTruth : Bool
    wikidataStatementCreatesTruth : Bool
    wikipediaArticleCreatesTruth : Bool
open WholeWikipediaExecutionPlan public

canonicalWholeWikipediaExecutionPlan : WholeWikipediaExecutionPlan
canonicalWholeWikipediaExecutionPlan =
  whole-wikipedia-execution-plan
    true true true true true true true true true true true true true true true true true
    false false false false

------------------------------------------------------------------------
-- Human-facing outputs requested by the attached Wikimedia discussion:
-- assertions, objects, logical soundness candidates, ontology gaps/joins,
-- crosslinks, bias-inspection surfaces, and mathematics verification queues.
------------------------------------------------------------------------

record WikipediaAuditProduct : Set where
  constructor wikipedia-audit-product
  field
    assertionTableReference : String
    objectEntityTableReference : String
    predicatePropertyTableReference : String
    sourceAttributionTableReference : String
    logicalConsistencyReportReference : String
    contradictionReportReference : String
    ontologyGapReportReference : String
    ontologyJoinReportReference : String
    missingCrosslinkReportReference : String
    biasInspectionReportReference : String
    mathVerificationReportReference : String
    unresolvedIdentityReportReference : String
    revisionDiffReportReference : String
open WikipediaAuditProduct public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data WholeWikipediaRunCreatesWholeWikipediaProof : Set where
data ParserCreatesAssertionTruth : Set where
data QidCreatesConceptIdentityWithoutResolution : Set where
data CategoryCreatesSubclassFact : Set where
data LinkCreatesLogicalImplication : Set where
data CitationCreatesSupportWithoutInspection : Set where
data PairwiseAgreementCreatesWorldTruth : Set where
data BiasDetectorCreatesBiasFact : Set where
data MathParserCreatesTheoremProof : Set where
data DerivedFindingAutoEditsWikipedia : Set where

wholeRunDoesNotCreateWholeWikipediaProof : WholeWikipediaRunCreatesWholeWikipediaProof → ⊥
wholeRunDoesNotCreateWholeWikipediaProof ()

parserDoesNotCreateAssertionTruth : ParserCreatesAssertionTruth → ⊥
parserDoesNotCreateAssertionTruth ()

qidNeedsResolution : QidCreatesConceptIdentityWithoutResolution → ⊥
qidNeedsResolution ()

categoryDoesNotCreateSubclassFact : CategoryCreatesSubclassFact → ⊥
categoryDoesNotCreateSubclassFact ()

linkDoesNotCreateLogicalImplication : LinkCreatesLogicalImplication → ⊥
linkDoesNotCreateLogicalImplication ()

citationNeedsInspection : CitationCreatesSupportWithoutInspection → ⊥
citationNeedsInspection ()

agreementDoesNotCreateWorldTruth : PairwiseAgreementCreatesWorldTruth → ⊥
agreementDoesNotCreateWorldTruth ()

biasCandidateIsNotBiasFact : BiasDetectorCreatesBiasFact → ⊥
biasCandidateIsNotBiasFact ()

mathParserDoesNotCreateProof : MathParserCreatesTheoremProof → ⊥
mathParserDoesNotCreateProof ()

derivedFindingDoesNotAutoEdit : DerivedFindingAutoEditsWikipedia → ⊥
derivedFindingDoesNotAutoEdit ()

record WikipediaWholeCorpusBoundary : Set where
  constructor wikipedia-whole-corpus-boundary
  field
    sourceRevisionFirstClass : Bool
    exactPassageFirstClass : Bool
    qidPropertyIdentityFirstClass : Bool
    sourceRoleFirstClass : Bool
    pnfAlternativesRetained : Bool
    itirUnresolvedPressureVisible : Bool
    algebraNeighborhoodIndexed : Bool
    incrementalRevisionRerunSupported : Bool
    reportsAreReviewSurfaces : Bool
    wholeCorpusRunEqualsProofOfWikipedia : Bool
    automaticWikipediaEditingAllowed : Bool
open WikipediaWholeCorpusBoundary public

canonicalWikipediaWholeCorpusBoundary : WikipediaWholeCorpusBoundary
canonicalWikipediaWholeCorpusBoundary =
  wikipedia-whole-corpus-boundary
    true true true true true true true true true false false

pnfIdentityBoundary : PNFIdentity.PredicateNormalFormWikimediaBoundary
pnfIdentityBoundary = PNFIdentity.canonicalPredicateNormalFormWikimediaBoundary

wikipediaIngestBoundary : WikiIngest.SensibLawWikipediaBoundary
wikipediaIngestBoundary = WikiIngest.canonicalSensibLawWikipediaBoundary

wikidataPredicateBoundary : WDPredicate.WikidataPNFBoundary
wikidataPredicateBoundary = WDPredicate.canonicalWikidataPNFBoundary

itirBoundary : ITIR.ITIRSuiteNormalizedParityBoundary
itirBoundary = ITIR.canonicalITIRSuiteNormalizedParityBoundary
