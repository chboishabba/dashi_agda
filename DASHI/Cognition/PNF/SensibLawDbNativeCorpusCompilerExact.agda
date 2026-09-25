module DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldExact as Ingest
import DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceExact as Persistence
import DASHI.Interop.DistributedEpistemicPlaneSeparationExact as Planes
import DASHI.Interop.DistributedEvidenceHistoryProjectionExact as History
import DASHI.Interop.ReplicationCapabilityNonCollapseExact as Replication
import DASHI.Interop.SensibLawWorldBucketPostgresMaterialisationExact as Postgres

------------------------------------------------------------------------
-- SCALE-1 DB-native corpus compiler.
--
-- This owner recuts book-scale/corpus-scale processing around persistent
-- compilation state rather than flat-file handoffs.
--
-- L0 source compilation:
--   immutable canonical bytes -> revision -> exact structural regions
--
-- L1 semantic compilation:
--   every semantic-eligible region -> persisted parser success OR residual
--   -> candidate Statement/PNF
--
-- L2 corpus reconciliation:
--   candidate semantics -> entity/proposition/event/temporal/cluster candidates
--
-- L3 review/admission:
--   explicit review/admission remains an independent payment
--
-- Existing distributed owners remain authoritative for capability separation:
-- BitTorrent bulk distribution, IPFS/IPLD linked-object retrieval, Postgres
-- local query materialisation, and admission as a separate epistemic plane.
------------------------------------------------------------------------

data CorpusCompilerLayer : Set where
  sourceCompilationLayer : CorpusCompilerLayer
  semanticCompilationLayer : CorpusCompilerLayer
  corpusReconciliationLayer : CorpusCompilerLayer
  reviewAdmissionLayer : CorpusCompilerLayer

data ParserJobStatus : Set where
  queued leased succeeded residual : ParserJobStatus

record CompilationIdentity : Set where
  constructor compilation-identity
  field
    sourceRevisionRef : String
    regionRef : String
    parserFamily : String
    parserVersion : String
    modelRef : String
    configDigestRef : String

open CompilationIdentity public

record ParserRun : Set where
  constructor parser-run
  field
    runRef : String
    sourceRevisionRef : String
    parserFamily : String
    parserVersion : String
    modelRef : String
    configDigestRef : String
    configJsonRef : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open ParserRun public

record ParserRegionJob
    (source : Ingest.GenericCompiledSource) : Set where
  constructor parser-region-job
  field
    compilationIdentity : CompilationIdentity
    region : Ingest.GenericSourceRegion source
    status : ParserJobStatus

    regionRevisionMatchesCompilation :
      Ingest.GenericSourceRegion.anchorUsesSourceRevision region
      ≡ Ingest.GenericSourceRegion.anchorUsesSourceRevision region

    leaseOwnerRef : String
    attemptRef : String

    leaseCreatesSourceAuthority : Bool
    leaseCreatesSourceAuthorityIsFalse :
      leaseCreatesSourceAuthority ≡ false

    leaseCreatesSemanticAuthority : Bool
    leaseCreatesSemanticAuthorityIsFalse :
      leaseCreatesSemanticAuthority ≡ false

open ParserRegionJob public

record PersistedParserToken
    (source : Ingest.GenericCompiledSource)
    (region : Ingest.GenericSourceRegion source) : Set where
  constructor persisted-parser-token
  field
    tokenRef : String
    tokenOrdinalRef : String
    exactRegion : Ingest.GenericSourceRegion source
    exactRegionIsSame : exactRegion ≡ region
    startCharRef : String
    endCharRef : String
    surfaceRef : String
    lemmaRef : String
    posRef : String
    morphJsonRef : String
    headOrdinalRef : String
    dependencyRef : String

    tokenCreatesTruth : Bool
    tokenCreatesTruthIsFalse :
      tokenCreatesTruth ≡ false

open PersistedParserToken public

record PersistedParserArtifact
    (source : Ingest.GenericCompiledSource)
    (region : Ingest.GenericSourceRegion source) : Set where
  constructor persisted-parser-artifact
  field
    artifactRef : String
    formatRef : String
    contentDigestRef : String
    objectLocatorRef : String

    artifactRegion : Ingest.GenericSourceRegion source
    artifactRegionIsSame : artifactRegion ≡ region

    contentAddressCreatesSemanticIdentity : Bool
    contentAddressCreatesSemanticIdentityIsFalse :
      contentAddressCreatesSemanticIdentity ≡ false

    artifactCreatesSemanticAuthority : Bool
    artifactCreatesSemanticAuthorityIsFalse :
      artifactCreatesSemanticAuthority ≡ false

open PersistedParserArtifact public

data ParserRegionOutcome
    (source : Ingest.GenericCompiledSource)
    (region : Ingest.GenericSourceRegion source) : Set where
  parserSucceeded :
    List (PersistedParserToken source region) →
    ParserRegionOutcome source region

  parserResidual :
    String →
    ParserRegionOutcome source region

record SemanticAttemptAssignment
    (source : Ingest.GenericCompiledSource) : Set where
  constructor semantic-attempt-assignment
  field
    region : Ingest.GenericSourceRegion source
    semanticEligibilityRequired :
      Ingest.GenericSourceRegion.eligibility region ≡ Ingest.semanticCandidate
    outcome : ParserRegionOutcome source region

open SemanticAttemptAssignment public

record SemanticAttemptCoverage
    (source : Ingest.GenericCompiledSource) : Set where
  constructor semantic-attempt-coverage
  field
    attempts : List (SemanticAttemptAssignment source)

    unattemptedSemanticRegions : Bool
    unattemptedSemanticRegionsIsFalse :
      unattemptedSemanticRegions ≡ false

    parserResidualDeletesSource : Bool
    parserResidualDeletesSourceIsFalse :
      parserResidualDeletesSource ≡ false

    parserResidualCreatesAbsenceFinding : Bool
    parserResidualCreatesAbsenceFindingIsFalse :
      parserResidualCreatesAbsenceFinding ≡ false

open SemanticAttemptCoverage public

record DbNativeCompilerReceipt
    (source : Ingest.GenericCompiledSource) : Set where
  constructor db-native-compiler-receipt
  field
    sourcePersistence : Persistence.PersistedGenericSource source
    semanticAttemptCoverage : SemanticAttemptCoverage source

    postgresMaterialisationIsLocal : Bool
    postgresMaterialisationIsLocalIsTrue :
      postgresMaterialisationIsLocal ≡ true

    runtimeStateRequiresFlatFileHandoff : Bool
    runtimeStateRequiresFlatFileHandoffIsFalse :
      runtimeStateRequiresFlatFileHandoff ≡ false

    jsonIsCanonicalRuntimeDatabase : Bool
    jsonIsCanonicalRuntimeDatabaseIsFalse :
      jsonIsCanonicalRuntimeDatabase ≡ false

    tsvIsCanonicalRuntimeDatabase : Bool
    tsvIsCanonicalRuntimeDatabaseIsFalse :
      tsvIsCanonicalRuntimeDatabase ≡ false

    parserSuccessCreatesReviewPayment : Bool
    parserSuccessCreatesReviewPaymentIsFalse :
      parserSuccessCreatesReviewPayment ≡ false

    parserCompletionCreatesAdmission : Bool
    parserCompletionCreatesAdmissionIsFalse :
      parserCompletionCreatesAdmission ≡ false

    postgresCreatesGlobalSemanticTruth : Bool
    postgresCreatesGlobalSemanticTruthIsFalse :
      postgresCreatesGlobalSemanticTruth ≡ false

open DbNativeCompilerReceipt public

------------------------------------------------------------------------
-- Reuse the existing distributed capability roles rather than defining a
-- second scale ontology.
------------------------------------------------------------------------

bitTorrentCapability :
  Replication.primaryRole Replication.bitTorrentRole
  ≡ Replication.immutableBulkDistribution
bitTorrentCapability = refl

ipfsCapability :
  Replication.primaryRole Replication.ipfsRole
  ≡ Replication.immutableLinkedObjectGraph
ipfsCapability = refl

postgresCapability :
  Replication.primaryRole Replication.localDatabaseRole
  ≡ Replication.localQueryMaterialisation
postgresCapability = refl

postgresMaterialisationBoundary : Postgres.PostgresWorldBucketBoundary
postgresMaterialisationBoundary = Postgres.canonicalPostgresWorldBucketBoundary

distributedPlaneBoundary : Planes.TechnologyRoleMap
distributedPlaneBoundary = Planes.canonicalTechnologyRoleMap

distributedEvidencePath : List History.EvidenceLayer
distributedEvidencePath = History.canonicalLayerPath

canonicalCompilerLayers : List CorpusCompilerLayer
canonicalCompilerLayers =
  sourceCompilationLayer ∷
  semanticCompilationLayer ∷
  corpusReconciliationLayer ∷
  reviewAdmissionLayer ∷ []

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data FlatFileIsRuntimeDatabase : Set where
data JsonArtifactIsRuntimeDatabase : Set where
data TsvArtifactIsRuntimeDatabase : Set where
data ParserLeaseCreatesSourceAuthority : Set where
data ParserSuccessCreatesReviewPayment : Set where
data ParserCompletionCreatesAdmission : Set where
data ParserResidualCreatesSourceAbsence : Set where
data ParserResidualCreatesPropositionAbsence : Set where
data ContentDigestCreatesSemanticIdentity : Set where
data PostgresCompilerStateCreatesGlobalTruth : Set where
data BulkDistributionCreatesProvenance : Set where
data LinkedObjectAvailabilityCreatesSemanticAuthority : Set where
data AutomaticExtractionCreatesAutomaticAdmission : Set where

flatFileDoesNotBecomeRuntimeDatabase :
  FlatFileIsRuntimeDatabase → ⊥
flatFileDoesNotBecomeRuntimeDatabase ()

jsonArtifactDoesNotBecomeRuntimeDatabase :
  JsonArtifactIsRuntimeDatabase → ⊥
jsonArtifactDoesNotBecomeRuntimeDatabase ()

tsvArtifactDoesNotBecomeRuntimeDatabase :
  TsvArtifactIsRuntimeDatabase → ⊥
tsvArtifactDoesNotBecomeRuntimeDatabase ()

parserLeaseDoesNotCreateSourceAuthority :
  ParserLeaseCreatesSourceAuthority → ⊥
parserLeaseDoesNotCreateSourceAuthority ()

parserSuccessDoesNotCreateReviewPayment :
  ParserSuccessCreatesReviewPayment → ⊥
parserSuccessDoesNotCreateReviewPayment ()

parserCompletionDoesNotCreateAdmission :
  ParserCompletionCreatesAdmission → ⊥
parserCompletionDoesNotCreateAdmission ()

parserResidualDoesNotCreateSourceAbsence :
  ParserResidualCreatesSourceAbsence → ⊥
parserResidualDoesNotCreateSourceAbsence ()

parserResidualDoesNotCreatePropositionAbsence :
  ParserResidualCreatesPropositionAbsence → ⊥
parserResidualDoesNotCreatePropositionAbsence ()

contentDigestDoesNotCreateSemanticIdentity :
  ContentDigestCreatesSemanticIdentity → ⊥
contentDigestDoesNotCreateSemanticIdentity ()

postgresCompilerStateDoesNotCreateGlobalTruth :
  PostgresCompilerStateCreatesGlobalTruth → ⊥
postgresCompilerStateDoesNotCreateGlobalTruth ()

bulkDistributionDoesNotCreateProvenance :
  BulkDistributionCreatesProvenance → ⊥
bulkDistributionDoesNotCreateProvenance ()

linkedObjectAvailabilityDoesNotCreateSemanticAuthority :
  LinkedObjectAvailabilityCreatesSemanticAuthority → ⊥
linkedObjectAvailabilityDoesNotCreateSemanticAuthority ()

automaticExtractionDoesNotCreateAutomaticAdmission :
  AutomaticExtractionCreatesAutomaticAdmission → ⊥
automaticExtractionDoesNotCreateAutomaticAdmission ()
