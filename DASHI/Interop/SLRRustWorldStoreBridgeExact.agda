module DASHI.Interop.SLRRustWorldStoreBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import DASHI.Interop.SLRPostgresWorldPersistenceExact

------------------------------------------------------------------------
-- RUST WORLD-STORE BRIDGE
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-world-store
--
-- Python remains the replaceable trained-spaCy observation boundary.
-- Rust owns high-volume world persistence and frontier retrieval.
-- PostgreSQL remains append-only storage/query substrate, never semantic
-- authority. Candidate semantic admission and promotion stay separate.
------------------------------------------------------------------------

record RustWorldStoreBoundary : Set where
  constructor rustWorldStoreBoundary
  field
    spacyExecutionRemainsLocalPythonBoundary : Bool
    pnfObservationProducedBeforePersistence : Bool
    highVolumePersistenceOwnedByRust : Bool
    postgresCopyUsesSingleGenericStage : Bool
    serverMergeIsConflictSafe : Bool
    serverMergeMayRewritePriorEvidence : Bool
    ndjsonIngressMayStreamRecordByRecord : Bool
    ndjsonIngressRequiresWholeInputBuffer : Bool
    legacyRoundReplayMayRemainBufferedCompatibilityPath : Bool
    latestFrontierReadOwnedByRust : Bool
    latestFrontierMayEmitRowBeforeWholeFrontierMaterialised : Bool
    latestFrontierRequiresWholeResultBuffer : Bool
    latestFrontierReadMayPromoteTruth : Bool
    postgresPerformsSLRSemanticProcessing : Bool
    databaseCredentialMayEnterReceipt : Bool
    pythonHeavyPersistenceIsRequired : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open RustWorldStoreBoundary public

canonicalRustWorldStoreBoundary : RustWorldStoreBoundary
canonicalRustWorldStoreBoundary =
  rustWorldStoreBoundary
    true true
    true true true false
    true false true
    true true false false
    false false false
    true false

record WorldStoreExecutionReceipt : Set where
  constructor worldStoreExecutionReceipt
  field
    rustBinaryResolved : Bool
    ingestNdjsonExecuted : Bool
    ingestNdjsonStreamingPaid : Bool
    legacyIngestRoundExecuted : Bool
    latestFrontierQueried : Bool
    frontierStreamingPaid : Bool
    pythonFallbackUsed : Bool
    persistenceCreatesSemanticAuthority : Bool
    frontierRankCreatesTruth : Bool

open WorldStoreExecutionReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PostgresPerformsSemanticProcessing : Set where
data RustPersistenceCreatesSemanticAuthority : Set where
data RustFrontierCreatesTruth : Set where
data ConflictMergeMayRewritePriorEvidence : Set where
data PythonHeavyPersistenceIsArchitecturallyRequired : Set where
data StreamingIngressRequiresWholeInputBuffer : Set where
data StreamingFrontierRequiresWholeResultBuffer : Set where

postgresDoesNotPerformSemanticProcessing : PostgresPerformsSemanticProcessing → ⊥
postgresDoesNotPerformSemanticProcessing ()

rustPersistenceDoesNotCreateSemanticAuthority : RustPersistenceCreatesSemanticAuthority → ⊥
rustPersistenceDoesNotCreateSemanticAuthority ()

rustFrontierDoesNotCreateTruth : RustFrontierCreatesTruth → ⊥
rustFrontierDoesNotCreateTruth ()

conflictMergeDoesNotRewritePriorEvidence : ConflictMergeMayRewritePriorEvidence → ⊥
conflictMergeDoesNotRewritePriorEvidence ()

pythonHeavyPersistenceIsNotRequired : PythonHeavyPersistenceIsArchitecturallyRequired → ⊥
pythonHeavyPersistenceIsNotRequired ()

streamingIngressDoesNotRequireWholeInput : StreamingIngressRequiresWholeInputBuffer → ⊥
streamingIngressDoesNotRequireWholeInput ()

streamingFrontierDoesNotRequireWholeResult : StreamingFrontierRequiresWholeResultBuffer → ⊥
streamingFrontierDoesNotRequireWholeResult ()
