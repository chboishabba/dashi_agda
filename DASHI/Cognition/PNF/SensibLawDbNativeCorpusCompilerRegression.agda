module DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerExact as Scale
import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldRegression as Fixture
import DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceRegression as PersistFixture
import DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceExact as Persistence

fixtureCompilationIdentity : Scale.CompilationIdentity
fixtureCompilationIdentity =
  Scale.compilation-identity
    "book-revision:fixture"
    "region:book:fixture:sentence:1"
    "spacy"
    "fixture-version"
    "fixture-model"
    "sha256:fixture-config"

fixtureJob : Scale.ParserRegionJob Fixture.fixtureSource
fixtureJob =
  Scale.parser-region-job
    fixtureCompilationIdentity
    Fixture.fixtureRegion
    Scale.succeeded
    refl
    "worker:fixture"
    "attempt:1"
    false refl
    false refl

fixtureToken :
  Scale.PersistedParserToken Fixture.fixtureSource Fixture.fixtureRegion
fixtureToken =
  Scale.persisted-parser-token
    "token:fixture:0"
    "0"
    Fixture.fixtureRegion
    refl
    "0"
    "5"
    "Alice"
    "alice"
    "PROPN"
    "{}"
    "1"
    "nsubj"
    false refl

fixtureAttempt :
  Scale.SemanticAttemptAssignment Fixture.fixtureSource
fixtureAttempt =
  Scale.semantic-attempt-assignment
    Fixture.fixtureRegion
    refl
    (Scale.parserSucceeded (fixtureToken ∷ []))

fixtureCoverage : Scale.SemanticAttemptCoverage Fixture.fixtureSource
fixtureCoverage =
  Scale.semantic-attempt-coverage
    (fixtureAttempt ∷ [])
    false refl
    false refl
    false refl

fixtureDbNativeReceipt : Scale.DbNativeCompilerReceipt Fixture.fixtureSource
fixtureDbNativeReceipt =
  Scale.db-native-compiler-receipt
    PersistFixture.fixtureSourcePersistence
    fixtureCoverage
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

fixtureHasNoUnattemptedSemanticRegions :
  Scale.SemanticAttemptCoverage.unattemptedSemanticRegions fixtureCoverage
  ≡ false
fixtureHasNoUnattemptedSemanticRegions = refl

fixturePostgresRemainsLocalMaterialisation :
  Scale.DbNativeCompilerReceipt.postgresMaterialisationIsLocal
    fixtureDbNativeReceipt
  ≡ true
fixturePostgresRemainsLocalMaterialisation = refl

fixtureAutomaticExtractionDoesNotAdmitTruth :
  Scale.DbNativeCompilerReceipt.parserCompletionCreatesAdmission
    fixtureDbNativeReceipt
  ≡ false
fixtureAutomaticExtractionDoesNotAdmitTruth = refl


fixturePersistedM12Candidate :
  Scale.PersistedM12CandidateProduct Fixture.fixtureSource Fixture.fixtureRegion
fixturePersistedM12Candidate =
  Scale.persisted-m12-candidate-product
    "statement:fixture"
    "candidate-pnf-batch:fixture"
    "db-parser:fixture"
    Fixture.fixtureRegion
    refl
    ("candidate:fixture:actor" ∷ "candidate:fixture:predicate" ∷ [])
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

fixtureCandidateReloadsWithoutAdmission :
  Scale.PersistedM12CandidateProduct.persistenceCreatesSemanticAdmission
    fixturePersistedM12Candidate
  ≡ false
fixtureCandidateReloadsWithoutAdmission = refl

fixtureCandidateReloadsWithoutTruth :
  Scale.PersistedM12CandidateProduct.persistenceCreatesClaimTruth
    fixturePersistedM12Candidate
  ≡ false
fixtureCandidateReloadsWithoutTruth = refl


fixtureReconciliationCandidate : Scale.CorpusReconciliationCandidate
fixtureReconciliationCandidate =
  Scale.corpus-reconciliation-candidate
    "entity-mention:fixture"
    "entity-fingerprint:fixture"
    "proposition-fingerprint:fixture"
    "event-fingerprint:fixture"
    "scale1:persistent-pnf-fingerprint:v1"
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

fixtureAutomaticReconciliationDoesNotCreateEventIdentity :
  Scale.CorpusReconciliationCandidate.createsEventIdentity
    fixtureReconciliationCandidate
  ≡ false
fixtureAutomaticReconciliationDoesNotCreateEventIdentity = refl

fixtureAutomaticReconciliationDoesNotCreatePropositionIdentity :
  Scale.CorpusReconciliationCandidate.createsPropositionIdentity
    fixtureReconciliationCandidate
  ≡ false
fixtureAutomaticReconciliationDoesNotCreatePropositionIdentity = refl


fixtureReviewProjection : Scale.ReconciliationReviewProjection
fixtureReviewProjection =
  Scale.reconciliation-review-projection
    "review-item:reconciliation:fixture"
    "proposition-fingerprint:fixture"
    "source-revision:fixture"
    "reconciliation-pressure:fixture"
    true refl
    false refl
    false refl
    false refl
    false refl

fixtureReviewProjectionDoesNotCreateEventAssembly :
  Scale.ReconciliationReviewProjection.createsEventAssembly fixtureReviewProjection
  ≡ false
fixtureReviewProjectionDoesNotCreateEventAssembly = refl

fixtureReviewProjectionDoesNotCreateTruth :
  Scale.ReconciliationReviewProjection.createsClaimTruth fixtureReviewProjection
  ≡ false
fixtureReviewProjectionDoesNotCreateTruth = refl


fixtureReviewedGroupingMaterialization :
  Scale.ReviewedGroupingMaterialization
fixtureReviewedGroupingMaterialization =
  Scale.reviewed-grouping-materialization
    "proposition:reconciliation:fixture"
    "proposition-fingerprint:fixture"
    "review-item:reconciliation:fixture"
    "review-command:scale1:fixture"
    ("claim:reconciliation:fixture" ∷ [])
    true refl
    false refl
    false refl
    false refl

fixtureGroupingReviewDoesNotPayClaimReview :
  Scale.ReviewedGroupingMaterialization.claimReviewPaid
    fixtureReviewedGroupingMaterialization
  ≡ false
fixtureGroupingReviewDoesNotPayClaimReview = refl

fixtureGroupingReviewDoesNotPayTruth :
  Scale.ReviewedGroupingMaterialization.claimTruthPaid
    fixtureReviewedGroupingMaterialization
  ≡ false
fixtureGroupingReviewDoesNotPayTruth = refl


fixtureAutoObservation : Scale.AutoEventObservationCandidate
fixtureAutoObservation =
  Scale.auto-event-observation-candidate
    "observation:scale1:fixture"
    "statement:fixture"
    "web"
    ("entity:fixture" ∷ [])
    ("temporal:fixture" ∷ [])
    ("event-fingerprint:fixture" ∷ [])
    true refl
    false refl
    false refl
    false refl
    false refl

fixtureAutoProposal : Scale.AutoEventJoinProposalProjection
fixtureAutoProposal =
  Scale.auto-event-join-proposal-projection
    "event-join-proposal:fixture"
    ("observation:scale1:a" ∷ "observation:scale1:b" ∷ [])
    ("document" ∷ "web" ∷ [])
    ("entity:fixture" ∷ "temporal:fixture" ∷ [])
    true refl
    false refl
    false refl
    false refl

fixtureAutoObservationDoesNotCreateEventIdentity :
  Scale.AutoEventObservationCandidate.createsEventIdentity fixtureAutoObservation
  ≡ false
fixtureAutoObservationDoesNotCreateEventIdentity = refl

fixtureAutoProposalRequiresReview :
  Scale.AutoEventJoinProposalProjection.requiresReview fixtureAutoProposal
  ≡ true
fixtureAutoProposalRequiresReview = refl

fixtureAutoProposalDoesNotCreateEventIdentity :
  Scale.AutoEventJoinProposalProjection.createsEventIdentity fixtureAutoProposal
  ≡ false
fixtureAutoProposalDoesNotCreateEventIdentity = refl


------------------------------------------------------------------------
-- Focused SCALE-1 book-ingest acceptance spine.
--
-- These are deliberately aliases of the existing owners: canonical source
-- weld, lossless region partition, durable reload, and DB-native semantic
-- attempt coverage.  The baseline receipt composes them; it does not define a
-- second source/partition/persistence ontology.
------------------------------------------------------------------------

fixtureBookReceiptCanonicalWeld :
  Fixture.fixtureRegionReallyUsesCanonicalRevision
  ≡ Fixture.fixtureRegionReallyUsesCanonicalRevision
fixtureBookReceiptCanonicalWeld = refl

fixtureBookReceiptLosslessPartition :
  PersistFixture.fixtureReloadPreservesPartition
  ≡ PersistFixture.fixtureReloadPreservesPartition
fixtureBookReceiptLosslessPartition = refl

fixtureBookReceiptCanonicalBytesReload :
  Persistence.PersistedGenericSource.canonicalBytesReloadable
    PersistFixture.fixtureSourcePersistence
  ≡ true
fixtureBookReceiptCanonicalBytesReload = refl

fixtureBookReceiptNoUnattemptedSemanticRegions :
  Scale.SemanticAttemptCoverage.unattemptedSemanticRegions fixtureCoverage
  ≡ false
fixtureBookReceiptNoUnattemptedSemanticRegions = refl

fixtureBookReceiptPersistenceDoesNotCreateAuthority :
  Persistence.PersistedGenericSource.persistenceCreatesSemanticAuthority
    PersistFixture.fixtureSourcePersistence
  ≡ false
fixtureBookReceiptPersistenceDoesNotCreateAuthority = refl

fixtureBookReceiptPersistenceDoesNotCreateApplicability :
  Persistence.PersistedGenericSource.persistenceCreatesApplicability
    PersistFixture.fixtureSourcePersistence
  ≡ false
fixtureBookReceiptPersistenceDoesNotCreateApplicability = refl

fixtureBookReceiptPersistenceDoesNotCreateTruth :
  Persistence.PersistedGenericSource.persistenceCreatesClaimTruth
    PersistFixture.fixtureSourcePersistence
  ≡ false
fixtureBookReceiptPersistenceDoesNotCreateTruth = refl


fixtureExactCompilerProductReuse : Scale.ExactCompilerProductReuse
fixtureExactCompilerProductReuse =
  Scale.exact-compiler-product-reuse
    "source-revision:fixture"
    "parser-run:fixture"
    "algorithm:fixture:v1"
    "consumer-scope:fixture"
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

fixtureExactReuseRequiresMatchingIdentity :
  Scale.ExactCompilerProductReuse.compilationIdentityMatched
    fixtureExactCompilerProductReuse
  ≡ true
fixtureExactReuseRequiresMatchingIdentity = refl

fixtureExactReuseRequiresCompleteProduct :
  Scale.ExactCompilerProductReuse.persistedProductComplete
    fixtureExactCompilerProductReuse
  ≡ true
fixtureExactReuseRequiresCompleteProduct = refl

fixtureExactReuseDoesNotAdmit :
  Scale.ExactCompilerProductReuse.createsSemanticAdmission
    fixtureExactCompilerProductReuse
  ≡ false
fixtureExactReuseDoesNotAdmit = refl

fixtureExactReuseDoesNotCreateTruth :
  Scale.ExactCompilerProductReuse.createsClaimTruth
    fixtureExactCompilerProductReuse
  ≡ false
fixtureExactReuseDoesNotCreateTruth = refl
