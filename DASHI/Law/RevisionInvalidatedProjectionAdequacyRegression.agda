module DASHI.Law.RevisionInvalidatedProjectionAdequacyRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.RevisionInvalidatedProjectionAdequacyExact as Revision

boundary : Revision.RevisionInvalidatedProjectionAdequacyBoundary
boundary = Revision.canonicalRevisionInvalidatedProjectionAdequacyBoundary

oldPaymentInvalidated :
  Revision.changedRevisionInvalidatesOldSourcePayment boundary ≡ true
oldPaymentInvalidated =
  Revision.changedRevisionInvalidatesOldSourcePaymentIsTrue boundary

staleSpanCannotPay :
  Revision.staleSpanMayContinuePayingFreshWorld boundary ≡ false
staleSpanCannotPay =
  Revision.staleSpanMayContinuePayingFreshWorldIsFalse boundary

projectionIdentityChanges :
  Revision.invalidatedProjectionGetsDistinctIdentity boundary ≡ true
projectionIdentityChanges =
  Revision.invalidatedProjectionGetsDistinctIdentityIsTrue boundary

oldProofCannotTransfer :
  Revision.oldFactorsThroughAutomaticallyTransfers boundary ≡ false
oldProofCannotTransfer =
  Revision.oldFactorsThroughAutomaticallyTransfersIsFalse boundary

researchMayReopen :
  Revision.invalidatedProjectionMayReopenResearch boundary ≡ true
researchMayReopen =
  Revision.invalidatedProjectionMayReopenResearchIsTrue boundary

rereviewMayRepay :
  Revision.rereviewMayRestoreFreshPayment boundary ≡ true
rereviewMayRepay =
  Revision.rereviewMayRestoreFreshPaymentIsTrue boundary
