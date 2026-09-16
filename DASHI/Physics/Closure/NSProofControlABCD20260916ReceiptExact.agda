module DASHI.Physics.Closure.NSProofControlABCD20260916ReceiptExact where

------------------------------------------------------------------------
-- NS PROOF-CONTROL A/B/C/D RECEIPT, 2026-09-16
--
-- Source / attribution boundary:
-- * Official A/B/C/D problem coordinates follow Charles L. Fefferman,
--   "Existence and Smoothness of the Navier--Stokes Equation", Clay
--   Mathematics Institute Millennium Problem description (2000), DOI not
--   assigned.
-- * C/D released-proof source receipts follow the OpenAI 2026 public
--   Navier--Stokes release and paired Lean repository as recorded by the
--   imported OpenAI2026 owners.  This file does not claim DASHI authorship of
--   that external proof and does not claim CMI prize adjudication.
-- * A/B bookkeeping is a DASHI proof-control reconstruction over existing
--   in-repo theorem/status owners.  It is not a new PDE estimate.
--
-- This owner is deliberately small: it makes the prose control plane
-- `Docs/roadmaps/NSProofControl20260915.md` recoverable from typed status
-- surfaces.  It records the current accounting frontier:
--
--   A: independent whole-space obligation; portability audit active.
--   B: active internal proof-discovery lane; d1b2 is the first nonlinear leaf.
--   C/D: released external theorem/source side present and Clay-coordinate
--        aligned; DASHI carrier/reconstruction/adjudication remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSGlobalFourAlternativeMissionExact as Global4
import DASHI.Physics.Closure.NSClayFourAlternativeReleasedProofBidiExact as Released4
import DASHI.Physics.Closure.NSOpenAI2026ComparatorClayCDSourceExactAlignment as CDAlign
import DASHI.Physics.Closure.NSOpenAI2026ReleasedClayCDTorus369BidiExact as CDTorus
import DASHI.Physics.Closure.NSABPortabilityBidiStatusExact as AB
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as D1b0
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as D1b1
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as D1b2

------------------------------------------------------------------------
-- A/B/C/D global mission and firewalls.
------------------------------------------------------------------------

abcdMissionImplemented : Bool
abcdMissionImplemented =
  Global4.roundGlobalFourAlternativeMissionImplemented

abcdAnyOneCriterionSeparated : Bool
abcdAnyOneCriterionSeparated =
  Global4.roundOfficialClayAnyOneCriterionSeparatedFromAllFourMission

abcdAllFourInternallyPaid : Bool
abcdAllFourInternallyPaid =
  Global4.roundGlobalAllFourInternallyPaid

aPortabilityAuditActive : Bool
aPortabilityAuditActive =
  AB.aPortabilityAuditActive

bToAImplicationAllowed : Bool
bToAImplicationAllowed =
  AB.bToAImplicationAllowed

aToBImplicationAllowed : Bool
aToBImplicationAllowed =
  AB.aToBImplicationAllowed

wholeSpaceTransportObserved : Bool
wholeSpaceTransportObserved =
  AB.wholeSpaceTransportObserved

------------------------------------------------------------------------
-- B lane: d1 has been narrowed to d1b2.
------------------------------------------------------------------------

bD1aDampedTangentClosed : Bool
bD1aDampedTangentClosed =
  D1a.fixedOutputDampedTangentDecompositionClosed

bD1b0CoherentWorkSplitClosed : Bool
bD1b0CoherentWorkSplitClosed =
  D1b0.fixedOutputCommutatorWorkDecompositionClosed

bD1b0CoherentCovarianceIsolated : Bool
bD1b0CoherentCovarianceIsolated =
  D1b0.commonRateCoherentCovarianceIsolationClosed

bD1b1EndpointCompilerClosed : Bool
bD1b1EndpointCompilerClosed =
  D1b1.fixedOutputMixedEndpointDerivativeCompilerClosed

bD1b1EndpointIdentityClosedGivenCalculus : Bool
bD1b1EndpointIdentityClosedGivenCalculus =
  D1b1.fixedOutputEndpointIdentityClosedGivenCalculus

bD1b1ConcreteEndpointFTCInstalled : Bool
bD1b1ConcreteEndpointFTCInstalled =
  D1b1.concreteEndpointFTCInstalled

bD1b2PairDifferenceAttachmentClosed : Bool
bD1b2PairDifferenceAttachmentClosed =
  D1b2.fixedOutputCovariancePairDifferenceAttachmentClosed

bD1b2QuantitativePaymentClosed : Bool
bD1b2QuantitativePaymentClosed =
  D1b2.quantitativePairDifferencePaymentClosed

bFirstNonlinearLeafIsD1b2 : Bool
bFirstNonlinearLeafIsD1b2 =
  AB.d1b2CoherentCovarianceCoordinateTracked

------------------------------------------------------------------------
-- C/D lane: source alignment closed, DASHI carrier/reconstruction still open.
------------------------------------------------------------------------

cExternalReleasedProofPresent : Bool
cExternalReleasedProofPresent =
  Released4.roundCExternalReleasedProofPresent4

dExternalReleasedProofPresent : Bool
dExternalReleasedProofPresent =
  Released4.roundDExternalReleasedProofPresent4

cdSourceAlignmentClosed : Bool
cdSourceAlignmentClosed =
  CDAlign.releasedComparatorCDSourceAlignmentClosed

cSourceExact : Bool
cSourceExact =
  CDAlign.roundCSourceExact

dSourceExact : Bool
dSourceExact =
  CDAlign.roundDSourceExact

cdReleasedFieldToDASHIFourierClosed : Bool
cdReleasedFieldToDASHIFourierClosed =
  CDAlign.releasedConcreteFieldToDASHIFourierClosed

cdReleasedForcingToR406Closed : Bool
cdReleasedForcingToR406Closed =
  CDAlign.releasedForcingToLiteralR406ComparisonClosed

cdDASHIIndependentReconstructionClosed : Bool
cdDASHIIndependentReconstructionClosed =
  CDAlign.DASHIIndependentAgdaReconstructionOfReleasedProofClosed

dPeriodicBase369FibreClosed : Bool
dPeriodicBase369FibreClosed =
  CDTorus.roundOAI2026PeriodicBase369FibreAlreadyClosed

cdPrizeOrDASHIDiscoveryClaimed : Bool
cdPrizeOrDASHIDiscoveryClaimed =
  Released4.roundClayPrizeCMIAwarded4

------------------------------------------------------------------------
-- Regression equalities for the control plane.
------------------------------------------------------------------------

abcdMissionImplementedIsTrue : abcdMissionImplemented ≡ true
abcdMissionImplementedIsTrue =
  Global4.roundGlobalFourAlternativeMissionImplementedIsTrue

abcdAnyOneCriterionSeparatedIsTrue :
  abcdAnyOneCriterionSeparated ≡ true
abcdAnyOneCriterionSeparatedIsTrue =
  Global4.roundOfficialClayAnyOneCriterionSeparatedFromAllFourMissionIsTrue

abcdAllFourInternallyPaidIsFalse :
  abcdAllFourInternallyPaid ≡ false
abcdAllFourInternallyPaidIsFalse =
  Global4.roundGlobalAllFourInternallyPaidIsFalse

aPortabilityAuditActiveIsTrue : aPortabilityAuditActive ≡ true
aPortabilityAuditActiveIsTrue =
  AB.aPortabilityAuditActiveIsTrue

bToAImplicationAllowedIsFalse : bToAImplicationAllowed ≡ false
bToAImplicationAllowedIsFalse =
  AB.bToAImplicationAllowedIsFalse

aToBImplicationAllowedIsFalse : aToBImplicationAllowed ≡ false
aToBImplicationAllowedIsFalse =
  AB.aToBImplicationAllowedIsFalse

wholeSpaceTransportObservedIsFalse : wholeSpaceTransportObserved ≡ false
wholeSpaceTransportObservedIsFalse =
  AB.wholeSpaceTransportObservedIsFalse

bD1aDampedTangentClosedIsTrue : bD1aDampedTangentClosed ≡ true
bD1aDampedTangentClosedIsTrue =
  D1a.fixedOutputDampedTangentDecompositionClosedIsTrue

bD1b0CoherentWorkSplitClosedIsTrue :
  bD1b0CoherentWorkSplitClosed ≡ true
bD1b0CoherentWorkSplitClosedIsTrue =
  D1b0.fixedOutputCommutatorWorkDecompositionClosedIsTrue

bD1b0CoherentCovarianceIsolatedIsTrue :
  bD1b0CoherentCovarianceIsolated ≡ true
bD1b0CoherentCovarianceIsolatedIsTrue =
  D1b0.commonRateCoherentCovarianceIsolationClosedIsTrue

bD1b1EndpointCompilerClosedIsTrue :
  bD1b1EndpointCompilerClosed ≡ true
bD1b1EndpointCompilerClosedIsTrue =
  D1b1.fixedOutputMixedEndpointDerivativeCompilerClosedIsTrue

bD1b1EndpointIdentityClosedGivenCalculusIsTrue :
  bD1b1EndpointIdentityClosedGivenCalculus ≡ true
bD1b1EndpointIdentityClosedGivenCalculusIsTrue =
  D1b1.fixedOutputEndpointIdentityClosedGivenCalculusIsTrue

bD1b1ConcreteEndpointFTCInstalledIsFalse :
  bD1b1ConcreteEndpointFTCInstalled ≡ false
bD1b1ConcreteEndpointFTCInstalledIsFalse =
  D1b1.concreteEndpointFTCInstalledIsFalse

bD1b2PairDifferenceAttachmentClosedIsTrue :
  bD1b2PairDifferenceAttachmentClosed ≡ true
bD1b2PairDifferenceAttachmentClosedIsTrue =
  D1b2.fixedOutputCovariancePairDifferenceAttachmentClosedIsTrue

bD1b2QuantitativePaymentClosedIsFalse :
  bD1b2QuantitativePaymentClosed ≡ false
bD1b2QuantitativePaymentClosedIsFalse =
  D1b2.quantitativePairDifferencePaymentClosedIsFalse

bFirstNonlinearLeafIsD1b2IsTrue : bFirstNonlinearLeafIsD1b2 ≡ true
bFirstNonlinearLeafIsD1b2IsTrue =
  AB.d1b2CoherentCovarianceCoordinateTrackedIsTrue

cExternalReleasedProofPresentIsTrue :
  cExternalReleasedProofPresent ≡ true
cExternalReleasedProofPresentIsTrue =
  Released4.roundCExternalReleasedProofPresent4IsTrue

dExternalReleasedProofPresentIsTrue :
  dExternalReleasedProofPresent ≡ true
dExternalReleasedProofPresentIsTrue =
  Released4.roundDExternalReleasedProofPresent4IsTrue

cdSourceAlignmentClosedIsTrue : cdSourceAlignmentClosed ≡ true
cdSourceAlignmentClosedIsTrue = refl

cSourceExactIsTrue : cSourceExact ≡ true
cSourceExactIsTrue =
  CDAlign.roundCSourceExactIsTrue

dSourceExactIsTrue : dSourceExact ≡ true
dSourceExactIsTrue =
  CDAlign.roundDSourceExactIsTrue

cdReleasedFieldToDASHIFourierClosedIsFalse :
  cdReleasedFieldToDASHIFourierClosed ≡ false
cdReleasedFieldToDASHIFourierClosedIsFalse = refl

cdReleasedForcingToR406ClosedIsFalse :
  cdReleasedForcingToR406Closed ≡ false
cdReleasedForcingToR406ClosedIsFalse = refl

cdDASHIIndependentReconstructionClosedIsFalse :
  cdDASHIIndependentReconstructionClosed ≡ false
cdDASHIIndependentReconstructionClosedIsFalse = refl

dPeriodicBase369FibreClosedIsTrue : dPeriodicBase369FibreClosed ≡ true
dPeriodicBase369FibreClosedIsTrue =
  CDTorus.roundOAI2026PeriodicBase369FibreAlreadyClosedIsTrue

cdPrizeOrDASHIDiscoveryClaimedIsFalse :
  cdPrizeOrDASHIDiscoveryClaimed ≡ false
cdPrizeOrDASHIDiscoveryClaimedIsFalse =
  Released4.roundClayPrizeCMIAwarded4IsFalse

nsProofControlABCD20260916ReceiptClosed : Bool
nsProofControlABCD20260916ReceiptClosed = true

nsProofControlABCD20260916PromotesClay : Bool
nsProofControlABCD20260916PromotesClay = false

nsProofControlABCD20260916ReceiptClosedIsTrue :
  nsProofControlABCD20260916ReceiptClosed ≡ true
nsProofControlABCD20260916ReceiptClosedIsTrue = refl

nsProofControlABCD20260916PromotesClayIsFalse :
  nsProofControlABCD20260916PromotesClay ≡ false
nsProofControlABCD20260916PromotesClayIsFalse = refl
