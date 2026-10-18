module DASHI.Core.CompactSemanticHistoryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CHECKPOINT + DELTA HISTORY REPRESENTATION
--
-- A temporal semantic history need not duplicate the full graph at every
-- commit. Checkpoints carry complete graph state; patch states carry a
-- parent-relative semantic delta sufficient for exact reconstruction.
------------------------------------------------------------------------

data SemanticHistoryStateKind : Set where
  semanticCheckpoint : SemanticHistoryStateKind
  semanticPatchState : SemanticHistoryStateKind

record SemanticHistoryStoragePolicy : Set where
  constructor semanticHistoryStoragePolicy
  field
    checkpointInterval : Nat
    fullGraphRequiredAtEveryCommit : Bool
    fullGraphRequiredAtEveryCommitIsFalse :
      fullGraphRequiredAtEveryCommit ≡ false

open SemanticHistoryStoragePolicy public

canonicalSemanticHistoryStoragePolicy :
  SemanticHistoryStoragePolicy
canonicalSemanticHistoryStoragePolicy =
  semanticHistoryStoragePolicy
    50
    false refl

data StableIdentityPayloadDisposition : Set where
  unchangedPayload : StableIdentityPayloadDisposition
  updatedPayload : StableIdentityPayloadDisposition

record CompactHistoryBoundary : Set where
  constructor compactHistoryBoundary
  field
    stableIdImpliesPayloadCannotChange : Bool
    stableIdImpliesPayloadCannotChangeIsFalse :
      stableIdImpliesPayloadCannotChange ≡ false

    patchMayOmitUpdatedStableIdPayload : Bool
    patchMayOmitUpdatedStableIdPayloadIsFalse :
      patchMayOmitUpdatedStableIdPayload ≡ false

    missingParentMayUsePatchWithoutCheckpoint : Bool
    missingParentMayUsePatchWithoutCheckpointIsFalse :
      missingParentMayUsePatchWithoutCheckpoint ≡ false

    compactRepresentationMayChangeSemanticGraph : Bool
    compactRepresentationMayChangeSemanticGraphIsFalse :
      compactRepresentationMayChangeSemanticGraph ≡ false

canonicalCompactHistoryBoundary : CompactHistoryBoundary
canonicalCompactHistoryBoundary =
  compactHistoryBoundary
    false refl
    false refl
    false refl
    false refl
