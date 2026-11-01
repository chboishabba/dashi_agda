module DASHI.Law.RevisionSlicedLatentWorldRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.RevisionSlicedLatentWorldExact as Slice

boundary : Slice.RevisionSlicedLatentWorldBoundary
boundary = Slice.canonicalRevisionSlicedLatentWorldBoundary

historyIsRetained :
  Slice.persistenceMayRetainHistoricalRevisions boundary ≡ true
historyIsRetained =
  Slice.persistenceMayRetainHistoricalRevisionsIsTrue boundary

sliceSelectsRevision :
  Slice.worldSliceSelectsOneReviewedRevisionPerSource boundary ≡ true
sliceSelectsRevision =
  Slice.worldSliceSelectsOneReviewedRevisionPerSourceIsTrue boundary

supersededContextAbsent :
  Slice.supersededRevisionOnlyContextVisibleInNewWorld boundary ≡ false
supersededContextAbsent =
  Slice.supersededRevisionOnlyContextVisibleInNewWorldIsFalse boundary

selectedContextTraverses :
  Slice.selectedRevisionContextMayParticipateInTraversal boundary ≡ true
selectedContextTraverses =
  Slice.selectedRevisionContextMayParticipateInTraversalIsTrue boundary

sliceDoesNotDeleteHistory :
  Slice.worldSliceDeletesHistoricalEvidence boundary ≡ false
sliceDoesNotDeleteHistory =
  Slice.worldSliceDeletesHistoricalEvidenceIsFalse boundary
