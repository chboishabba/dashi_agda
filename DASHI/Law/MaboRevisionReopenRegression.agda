module DASHI.Law.MaboRevisionReopenRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.MaboRevisionReopenExact as Reopen

boundary : Reopen.MaboRevisionReopenBoundary
boundary = Reopen.canonicalMaboRevisionReopenBoundary

contextBeforeIdentity :
  Reopen.revisionChangeReopensContextBeforeIdentity boundary ≡ true
contextBeforeIdentity =
  Reopen.revisionChangeReopensContextBeforeIdentityIsTrue boundary

lookupDoesNotReview :
  Reopen.latestRevisionLookupPaysContextReview boundary ≡ false
lookupDoesNotReview =
  Reopen.latestRevisionLookupPaysContextReviewIsFalse boundary

failedLookupIsNotUnchanged :
  Reopen.latestRevisionLookupFailureMayCountAsUnchanged boundary ≡ false
failedLookupIsNotUnchanged =
  Reopen.latestRevisionLookupFailureMayCountAsUnchangedIsFalse boundary

truncatedProbeIsNotClosed :
  Reopen.truncatedRevisionProbeMayCloseFrontier boundary ≡ false
truncatedProbeIsNotClosed =
  Reopen.truncatedRevisionProbeMayCloseFrontierIsFalse boundary

acquisitionDoesNotReview :
  Reopen.exactR1AcquisitionPaysContextReview boundary ≡ false
acquisitionDoesNotReview =
  Reopen.exactR1AcquisitionPaysContextReviewIsFalse boundary

reviewMayRecompute :
  Reopen.explicitR1ContextReviewMayTriggerRecomputation boundary ≡ true
reviewMayRecompute =
  Reopen.explicitR1ContextReviewMayTriggerRecomputationIsTrue boundary

freshIdentityNeedsReviewedDelta :
  Reopen.freshIdentityResidualRequiresReviewedDelta boundary ≡ true
freshIdentityNeedsReviewedDelta =
  Reopen.freshIdentityResidualRequiresReviewedDeltaIsTrue boundary

usesGenericKernel :
  Reopen.reviewedIdentityDeltaUsesGenericKernel boundary ≡ true
usesGenericKernel =
  Reopen.reviewedIdentityDeltaUsesGenericKernelIsTrue boundary