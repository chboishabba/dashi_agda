module DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerExact as Scale
import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldRegression as Fixture
import DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceRegression as PersistFixture

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
