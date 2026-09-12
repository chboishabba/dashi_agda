module DASHI.Interop.SLRPostgresWorldPersistenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- POSTGRES WORLD-RESEARCH PERSISTENCE BOUNDARY
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

record GraphOnlyWikimediaPersistenceBoundary : Set where
  constructor graphOnlyWikimediaPersistenceBoundary
  field
    graphSidecarIsSufficientForBoundedMerge : Bool
    copiedCandidateWorldSnapshotRequiredForBoundedMerge : Bool
    graphOnlyMaySkipCopiedWorldSerialization : Bool
    skippedSerializationLosesSemanticAuthority : Bool
    skippedSerializationPromotesTruth : Bool

open GraphOnlyWikimediaPersistenceBoundary public

canonicalGraphOnlyWikimediaPersistenceBoundary : GraphOnlyWikimediaPersistenceBoundary
canonicalGraphOnlyWikimediaPersistenceBoundary =
  graphOnlyWikimediaPersistenceBoundary true false true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PostgresIsSemanticAuthority : Set where
data PostgresCreatesClaimTruth : Set where
data PostgresCreatesOntologyTruth : Set where
data DatabaseUrlMayBePublishedInReceipt : Set where
data ConflictSafeWriteMayDeletePriorEvidence : Set where
data ConflictingReplayMayRewritePriorEvidence : Set where
data CopiedWorldSnapshotRequiredForGraphMerge : Set where

postgresIsNotSemanticAuthority : PostgresIsSemanticAuthority → ⊥
postgresIsNotSemanticAuthority ()

postgresDoesNotCreateClaimTruth : PostgresCreatesClaimTruth → ⊥
postgresDoesNotCreateClaimTruth ()

postgresDoesNotCreateOntologyTruth : PostgresCreatesOntologyTruth → ⊥
postgresDoesNotCreateOntologyTruth ()

databaseUrlDoesNotEnterReceipt : DatabaseUrlMayBePublishedInReceipt → ⊥
databaseUrlDoesNotEnterReceipt ()

conflictSafeWriteDoesNotDeleteEvidence : ConflictSafeWriteMayDeletePriorEvidence → ⊥
conflictSafeWriteDoesNotDeleteEvidence ()

conflictingReplayDoesNotRewriteEvidence : ConflictingReplayMayRewritePriorEvidence → ⊥
conflictingReplayDoesNotRewriteEvidence ()

graphMergeDoesNotRequireCopiedWorldSnapshot : CopiedWorldSnapshotRequiredForGraphMerge → ⊥
graphMergeDoesNotRequireCopiedWorldSnapshot ()
