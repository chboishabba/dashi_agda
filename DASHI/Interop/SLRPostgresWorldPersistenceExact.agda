module DASHI.Interop.SLRPostgresWorldPersistenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- POSTGRES WORLD-RESEARCH PERSISTENCE BOUNDARY
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_world_pg_store.py
--   tools/slr-discourse-reconstruct/run_world_research_budgeted_round.sh
--   tools/slr-discourse-reconstruct/slr_world_round_accounting.py
--
-- spaCy / SLR / PNF processing remains local.  PostgreSQL is durable,
-- append-only/idempotent persistence and later query substrate only.
------------------------------------------------------------------------

record PostgresWorldPersistenceBoundary : Set where
  constructor postgresWorldPersistenceBoundary
  field
    databaseUrlComesFromEnvironment : Bool
    databaseUrlMayEnterReceipt : Bool
    sourceManifestationIdentityStable : Bool
    pnfCandidateIdentityStable : Bool
    worldAtomIdentityStable : Bool
    gapIdentityStableWithinIteration : Bool
    obligationIdentityStableWithinIteration : Bool
    routeActionIdentityStable : Bool
    iterationIdentityStable : Bool
    writesConflictSafeAndIdempotent : Bool
    conflictingReplayRewritesPriorEvidence : Bool
    writesDeletePriorEvidence : Bool
    postgresPersistenceCreatesSemanticAuthority : Bool
    postgresPersistenceCreatesClaimTruth : Bool
    postgresPersistenceCreatesOntologyTruth : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open PostgresWorldPersistenceBoundary public

canonicalPostgresWorldPersistenceBoundary : PostgresWorldPersistenceBoundary
canonicalPostgresWorldPersistenceBoundary =
  postgresWorldPersistenceBoundary
    true false
    true true true true true true true
    true false false
    false false false
    true false

record PostgresBulkPersistenceBoundary : Set where
  constructor postgresBulkPersistenceBoundary
  field
    spacyRunsLocally : Bool
    slrRunsLocally : Bool
    pnfProjectionRunsLocally : Bool
    postgresRunsSemanticProcessing : Bool
    copyUsesTransactionLocalStaging : Bool
    stagingMergeUsesConflictDoNothing : Bool
    copyStageMayRewriteExistingEvidence : Bool
    rowwiseExecutemanyIsProductionHotPath : Bool
    rowwiseFallbackMayRemainForDebug : Bool

open PostgresBulkPersistenceBoundary public

canonicalPostgresBulkPersistenceBoundary : PostgresBulkPersistenceBoundary
canonicalPostgresBulkPersistenceBoundary =
  postgresBulkPersistenceBoundary
    true true true false
    true true false
    false true

record GraphOnlyWikimediaPersistenceBoundary : Set where
  constructor graphOnlyWikimediaPersistenceBoundary
  field
    graphSidecarIsSufficientForBoundedMerge : Bool
    copiedCandidateWorldSnapshotRequiredForBoundedMerge : Bool
    graphOnlyMaySkipCopiedWorldSerialization : Bool
    boundedRoundInvokesTrueGraphOnly : Bool
    skippedSerializationLosesSemanticAuthority : Bool
    skippedSerializationPromotesTruth : Bool

open GraphOnlyWikimediaPersistenceBoundary public

canonicalGraphOnlyWikimediaPersistenceBoundary : GraphOnlyWikimediaPersistenceBoundary
canonicalGraphOnlyWikimediaPersistenceBoundary =
  graphOnlyWikimediaPersistenceBoundary true false true true false false

record RoundWorldGrowthAccountingBoundary : Set where
  constructor roundWorldGrowthAccountingBoundary
  field
    structuralGrowthMeasuredSeparately : Bool
    articlePnfGrowthMeasuredSeparately : Bool
    totalGrowthEqualsComponentSum : Bool
    atomGrowthCreatesClaimTruth : Bool

open RoundWorldGrowthAccountingBoundary public

canonicalRoundWorldGrowthAccountingBoundary : RoundWorldGrowthAccountingBoundary
canonicalRoundWorldGrowthAccountingBoundary =
  roundWorldGrowthAccountingBoundary true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PostgresIsSemanticAuthority : Set where
data PostgresCreatesClaimTruth : Set where
data PostgresCreatesOntologyTruth : Set where
data PostgresRunsSemanticProcessing : Set where
data DatabaseUrlMayBePublishedInReceipt : Set where
data ConflictSafeWriteMayDeletePriorEvidence : Set where
data ConflictingReplayMayRewritePriorEvidence : Set where
data CopyStageMayRewritePriorEvidence : Set where
data CopiedWorldSnapshotRequiredForGraphMerge : Set where
data AtomGrowthCreatesClaimTruth : Set where

postgresIsNotSemanticAuthority : PostgresIsSemanticAuthority → ⊥
postgresIsNotSemanticAuthority ()

postgresDoesNotCreateClaimTruth : PostgresCreatesClaimTruth → ⊥
postgresDoesNotCreateClaimTruth ()

postgresDoesNotCreateOntologyTruth : PostgresCreatesOntologyTruth → ⊥
postgresDoesNotCreateOntologyTruth ()

postgresDoesNotRunSemanticProcessing : PostgresRunsSemanticProcessing → ⊥
postgresDoesNotRunSemanticProcessing ()

databaseUrlDoesNotEnterReceipt : DatabaseUrlMayBePublishedInReceipt → ⊥
databaseUrlDoesNotEnterReceipt ()

conflictSafeWriteDoesNotDeleteEvidence : ConflictSafeWriteMayDeletePriorEvidence → ⊥
conflictSafeWriteDoesNotDeleteEvidence ()

conflictingReplayDoesNotRewriteEvidence : ConflictingReplayMayRewritePriorEvidence → ⊥
conflictingReplayDoesNotRewriteEvidence ()

copyStageDoesNotRewriteEvidence : CopyStageMayRewritePriorEvidence → ⊥
copyStageDoesNotRewriteEvidence ()

graphMergeDoesNotRequireCopiedWorldSnapshot : CopiedWorldSnapshotRequiredForGraphMerge → ⊥
graphMergeDoesNotRequireCopiedWorldSnapshot ()

atomGrowthDoesNotCreateClaimTruth : AtomGrowthCreatesClaimTruth → ⊥
atomGrowthDoesNotCreateClaimTruth ()
