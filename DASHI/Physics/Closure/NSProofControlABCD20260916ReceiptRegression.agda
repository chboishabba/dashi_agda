module DASHI.Physics.Closure.NSProofControlABCD20260916ReceiptRegression where

------------------------------------------------------------------------
-- Regression for the 2026-09-16 A/B/C/D proof-control receipt.
--
-- This checks the bookkeeping surface only.  It must preserve the split:
-- A/B remain independent, B's first nonlinear leaf is d1b2, C/D source
-- alignment is recorded, and no Clay/prize promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSProofControlABCD20260916ReceiptExact as R

abcdMissionImplemented :
  R.abcdMissionImplemented ≡ true
abcdMissionImplemented =
  R.abcdMissionImplementedIsTrue

abcdAnyOneCriterionSeparated :
  R.abcdAnyOneCriterionSeparated ≡ true
abcdAnyOneCriterionSeparated =
  R.abcdAnyOneCriterionSeparatedIsTrue

abcdAllFourInternallyPaidIsFalse :
  R.abcdAllFourInternallyPaid ≡ false
abcdAllFourInternallyPaidIsFalse =
  R.abcdAllFourInternallyPaidIsFalse

aPortabilityAuditActive :
  R.aPortabilityAuditActive ≡ true
aPortabilityAuditActive =
  R.aPortabilityAuditActiveIsTrue

bToAImplicationBlocked :
  R.bToAImplicationAllowed ≡ false
bToAImplicationBlocked =
  R.bToAImplicationAllowedIsFalse

aToBImplicationBlocked :
  R.aToBImplicationAllowed ≡ false
aToBImplicationBlocked =
  R.aToBImplicationAllowedIsFalse

bD1aDampedTangentClosed :
  R.bD1aDampedTangentClosed ≡ true
bD1aDampedTangentClosed =
  R.bD1aDampedTangentClosedIsTrue

bD1b0CoherentWorkSplitClosed :
  R.bD1b0CoherentWorkSplitClosed ≡ true
bD1b0CoherentWorkSplitClosed =
  R.bD1b0CoherentWorkSplitClosedIsTrue

bD1b1EndpointCompilerClosed :
  R.bD1b1EndpointCompilerClosed ≡ true
bD1b1EndpointCompilerClosed =
  R.bD1b1EndpointCompilerClosedIsTrue

bD1b1ConcreteEndpointFTCStillOpen :
  R.bD1b1ConcreteEndpointFTCInstalled ≡ false
bD1b1ConcreteEndpointFTCStillOpen =
  R.bD1b1ConcreteEndpointFTCInstalledIsFalse

bD1b2PairDifferenceAttachmentClosed :
  R.bD1b2PairDifferenceAttachmentClosed ≡ true
bD1b2PairDifferenceAttachmentClosed =
  R.bD1b2PairDifferenceAttachmentClosedIsTrue

bD1b2QuantitativePaymentStillOpen :
  R.bD1b2QuantitativePaymentClosed ≡ false
bD1b2QuantitativePaymentStillOpen =
  R.bD1b2QuantitativePaymentClosedIsFalse

bFirstNonlinearLeafIsD1b2 :
  R.bFirstNonlinearLeafIsD1b2 ≡ true
bFirstNonlinearLeafIsD1b2 =
  R.bFirstNonlinearLeafIsD1b2IsTrue

cExternalReleasedProofPresent :
  R.cExternalReleasedProofPresent ≡ true
cExternalReleasedProofPresent =
  R.cExternalReleasedProofPresentIsTrue

dExternalReleasedProofPresent :
  R.dExternalReleasedProofPresent ≡ true
dExternalReleasedProofPresent =
  R.dExternalReleasedProofPresentIsTrue

cdSourceAlignmentClosed :
  R.cdSourceAlignmentClosed ≡ true
cdSourceAlignmentClosed =
  R.cdSourceAlignmentClosedIsTrue

cdReleasedFieldToDASHIFourierStillOpen :
  R.cdReleasedFieldToDASHIFourierClosed ≡ false
cdReleasedFieldToDASHIFourierStillOpen =
  R.cdReleasedFieldToDASHIFourierClosedIsFalse

cdReleasedForcingToR406StillOpen :
  R.cdReleasedForcingToR406Closed ≡ false
cdReleasedForcingToR406StillOpen =
  R.cdReleasedForcingToR406ClosedIsFalse

cdDASHIIndependentReconstructionStillOpen :
  R.cdDASHIIndependentReconstructionClosed ≡ false
cdDASHIIndependentReconstructionStillOpen =
  R.cdDASHIIndependentReconstructionClosedIsFalse

dPeriodicBase369FibreClosed :
  R.dPeriodicBase369FibreClosed ≡ true
dPeriodicBase369FibreClosed =
  R.dPeriodicBase369FibreClosedIsTrue

cdPrizeOrDASHIDiscoveryNotClaimed :
  R.cdPrizeOrDASHIDiscoveryClaimed ≡ false
cdPrizeOrDASHIDiscoveryNotClaimed =
  R.cdPrizeOrDASHIDiscoveryClaimedIsFalse

receiptClosed :
  R.nsProofControlABCD20260916ReceiptClosed ≡ true
receiptClosed =
  R.nsProofControlABCD20260916ReceiptClosedIsTrue

receiptDoesNotPromoteClay :
  R.nsProofControlABCD20260916PromotesClay ≡ false
receiptDoesNotPromoteClay =
  R.nsProofControlABCD20260916PromotesClayIsFalse
