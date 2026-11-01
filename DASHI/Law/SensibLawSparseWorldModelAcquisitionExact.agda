module DASHI.Law.SensibLawSparseWorldModelAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawCorpusProducerRoutingExact as Corpus
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Result

------------------------------------------------------------------------
-- SPARSE WORLD-MODEL ACQUISITION
--
-- Broad cheap compilation and consumer-driven deep semantic resolution are
-- distinct. The world model can start sparse and grow as the memoised closure
-- of prior proof searches.
------------------------------------------------------------------------

data CompilationDepth : Set where
  canonicalTextOnly : CompilationDepth
  parserAnnotationGraph : CompilationDepth
  basicPNFStructure : CompilationDepth
  citationTopology : CompilationDepth
  deepSemanticResolution : CompilationDepth
  reviewedProofPayment : CompilationDepth


record CompiledCorpusArtifact : Set₁ where
  constructor compiledCorpusArtifact
  field
    documentReference : String
    corpusClass : Corpus.CorpusClass
    depth : CompilationDepth
    immutableProvenanceReference : String
    parserProfileReference : String
    basicPNFReference : String
    citationTopologyReference : String
    semanticResolutionReference : String
    artifactReference : String

open CompiledCorpusArtifact public

data ResolutionPolicy : Set where
  eagerCheapStructure : ResolutionPolicy
  consumerDrivenDeepening : ResolutionPolicy
  explicitAuditDeepening : ResolutionPolicy
  noDeepeningRequired : ResolutionPolicy


record CorpusDeepeningDemand : Set₁ where
  constructor corpusDeepeningDemand
  field
    consumerReference : String
    documentReference : String
    priorDepth : CompilationDepth
    requestedDepth : CompilationDepth
    policy : ResolutionPolicy
    liveResidualReference : String
    expectedContributionReference : String
    demandReference : String

open CorpusDeepeningDemand public

------------------------------------------------------------------------
-- World-memory accumulation.
------------------------------------------------------------------------

record WorldModelSnapshot : Set₁ where
  constructor worldModelSnapshot
  field
    snapshotReference : String
    compiledArtifacts : List CompiledCorpusArtifact
    priorResearchReferences : List String
    openResidualReferences : List String
    sourceCoverageReference : String

open WorldModelSnapshot public

record WorldModelExtension
    (prior posterior : WorldModelSnapshot) : Set₁ where
  constructor worldModelExtension
  field
    priorArtifactsRetainedReceipt : Set
    newArtifactsReference : List String
    newResearchReferences : List String
    noSilentPriorRewriteReceipt : Set
    extensionReference : String

open WorldModelExtension public

record MemoisedResearchClosure : Set₁ where
  constructor memoisedResearchClosure
  field
    consumerReference : String
    sourceSnapshotReference : String
    resultingSnapshotReference : String
    retrievedDocumentReferences : List String
    assessedFrontierDeltas : List Result.SearchFrontierDelta
    reusableQueryVocabularyReference : String
    reusableAuthorityNeighbourhoodReference : String
    closureReference : String

open MemoisedResearchClosure public

------------------------------------------------------------------------
-- Search mode changes as the local world grows.
------------------------------------------------------------------------

data WorldSearchMode : Set where
  externalSparseDiscovery : WorldSearchMode
  hybridLocalExternalSearch : WorldSearchMode
  directLocalGraphProofSearch : WorldSearchMode


record WorldSearchReadiness : Set where
  constructor worldSearchReadiness
  field
    snapshotReference : String
    mode : WorldSearchMode
    localAuthorityCoverageReference : String
    localLexicalCoverageReference : String
    localProofPaymentCoverageReference : String
    readinessReference : String

open WorldSearchReadiness public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ParsingEverythingMeansResolvingEverything : Set where
data ParsedDocumentMeansWorldTruth : Set where
data WorldModelMustBeCompleteBeforeProofSearch : Set where
data MoreCompiledDocumentsAutomaticallyCloseResidual : Set where
data MemoisedResearchMayRewritePriorProvenance : Set where

parsingDoesNotMeanResolution : ParsingEverythingMeansResolvingEverything → ⊥
parsingDoesNotMeanResolution ()

parsedDocumentDoesNotMeanTruth : ParsedDocumentMeansWorldTruth → ⊥
parsedDocumentDoesNotMeanTruth ()

worldNeedNotBeCompleteBeforeSearch : WorldModelMustBeCompleteBeforeProofSearch → ⊥
worldNeedNotBeCompleteBeforeSearch ()

moreCompiledDocumentsDoNotAutoCloseResidual :
  MoreCompiledDocumentsAutomaticallyCloseResidual → ⊥
moreCompiledDocumentsDoNotAutoCloseResidual ()

memoisedResearchDoesNotRewritePriorProvenance :
  MemoisedResearchMayRewritePriorProvenance → ⊥
memoisedResearchDoesNotRewritePriorProvenance ()

record SparseWorldBoundary : Set where
  constructor sparseWorldBoundary
  field
    cheapStructureMayBeEager : Bool
    cheapStructureMayBeEagerIsTrue : cheapStructureMayBeEager ≡ true
    deepResolutionMayBeConsumerDriven : Bool
    deepResolutionMayBeConsumerDrivenIsTrue : deepResolutionMayBeConsumerDriven ≡ true
    completeWorldRequiredBeforeUse : Bool
    completeWorldRequiredBeforeUseIsFalse : completeWorldRequiredBeforeUse ≡ false
    researchResultsMayAccumulateIntoWorld : Bool
    researchResultsMayAccumulateIntoWorldIsTrue : researchResultsMayAccumulateIntoWorld ≡ true
    parsingEqualsTruth : Bool
    parsingEqualsTruthIsFalse : parsingEqualsTruth ≡ false

canonicalSparseWorldBoundary : SparseWorldBoundary
canonicalSparseWorldBoundary =
  sparseWorldBoundary true refl true refl false refl true refl false refl
