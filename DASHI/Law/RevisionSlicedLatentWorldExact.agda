module DASHI.Law.RevisionSlicedLatentWorldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S18: append-only persistence is not the same thing as one legal world.
--
-- Historical reviewed context at R0 and R1 may both remain durable.  A legal
-- world slice selects one reviewed manifestation per source; context supported
-- only by a superseded manifestation is absent from the newer world traversal.
------------------------------------------------------------------------

data Revision : Set where r0 r1 : Revision

data ContextEdge : Set where
  edgeOnlyR0 : ContextEdge
  edgeBoth : ContextEdge
  edgeOnlyR1 : ContextEdge

supports : Revision → ContextEdge → Bool
supports r0 edgeOnlyR0 = true
supports r0 edgeBoth = true
supports r0 edgeOnlyR1 = false
supports r1 edgeOnlyR0 = false
supports r1 edgeBoth = true
supports r1 edgeOnlyR1 = true

visibleInSlice : Revision → ContextEdge → Bool
visibleInSlice revision edge = supports revision edge

r0OnlyEdgeVisibleAtR0 :
  visibleInSlice r0 edgeOnlyR0 ≡ true
r0OnlyEdgeVisibleAtR0 = refl

r0OnlyEdgeAbsentAtR1 :
  visibleInSlice r1 edgeOnlyR0 ≡ false
r0OnlyEdgeAbsentAtR1 = refl

sharedEdgeVisibleAtR1 :
  visibleInSlice r1 edgeBoth ≡ true
sharedEdgeVisibleAtR1 = refl

r1OnlyEdgeVisibleAtR1 :
  visibleInSlice r1 edgeOnlyR1 ≡ true
r1OnlyEdgeVisibleAtR1 = refl

data AppendOnlyHistoryAutomaticallyCurrentWorld : Set where
data SupersededContextAutomaticallyVisible : Set where

historyDoesNotAutomaticallyDefineCurrentWorld :
  AppendOnlyHistoryAutomaticallyCurrentWorld → ⊥
historyDoesNotAutomaticallyDefineCurrentWorld ()

supersededContextCannotAutomaticallyRemainVisible :
  SupersededContextAutomaticallyVisible → ⊥
supersededContextCannotAutomaticallyRemainVisible ()

record RevisionSlicedLatentWorldBoundary : Set where
  constructor revisionSlicedLatentWorldBoundary
  field
    persistenceMayRetainHistoricalRevisions : Bool
    persistenceMayRetainHistoricalRevisionsIsTrue :
      persistenceMayRetainHistoricalRevisions ≡ true

    worldSliceSelectsOneReviewedRevisionPerSource : Bool
    worldSliceSelectsOneReviewedRevisionPerSourceIsTrue :
      worldSliceSelectsOneReviewedRevisionPerSource ≡ true

    supersededRevisionOnlyContextVisibleInNewWorld : Bool
    supersededRevisionOnlyContextVisibleInNewWorldIsFalse :
      supersededRevisionOnlyContextVisibleInNewWorld ≡ false

    selectedRevisionContextMayParticipateInTraversal : Bool
    selectedRevisionContextMayParticipateInTraversalIsTrue :
      selectedRevisionContextMayParticipateInTraversal ≡ true

    worldSliceDeletesHistoricalEvidence : Bool
    worldSliceDeletesHistoricalEvidenceIsFalse :
      worldSliceDeletesHistoricalEvidence ≡ false

    worldSliceCreatesSemanticAuthority : Bool
    worldSliceCreatesSemanticAuthorityIsFalse :
      worldSliceCreatesSemanticAuthority ≡ false

    worldSliceCreatesClaimTruth : Bool
    worldSliceCreatesClaimTruthIsFalse :
      worldSliceCreatesClaimTruth ≡ false

open RevisionSlicedLatentWorldBoundary public

canonicalRevisionSlicedLatentWorldBoundary :
  RevisionSlicedLatentWorldBoundary
canonicalRevisionSlicedLatentWorldBoundary =
  revisionSlicedLatentWorldBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
