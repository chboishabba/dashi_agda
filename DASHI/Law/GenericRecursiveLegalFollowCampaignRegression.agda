module DASHI.Law.GenericRecursiveLegalFollowCampaignRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Law.GenericRecursiveLegalFollowCampaignExact as Recursive

boundary :
  Recursive.GenericRecursiveCampaignBoundary
boundary =
  Recursive.canonicalGenericRecursiveCampaignBoundary

typedTracePersists :
  Recursive.finalTypedTraceIsPersisted boundary ≡ true
typedTracePersists =
  Recursive.finalTypedTraceIsPersistedIsTrue boundary

continuationRestoresTypedWorld :
  Recursive.continuationRestoresTypedTrace boundary ≡ true
continuationRestoresTypedWorld =
  Recursive.continuationRestoresTypedTraceIsTrue boundary

frontierIsFreshAfterAcceptedHop :
  Recursive.freshFrontierRecomputedAfterAcceptedHop boundary ≡ true
frontierIsFreshAfterAcceptedHop =
  Recursive.freshFrontierRecomputedAfterAcceptedHopIsTrue boundary

fixedQueueIsNotTheController :
  Recursive.fixedUpfrontQueueConsumed boundary ≡ false
fixedQueueIsNotTheController =
  Recursive.fixedUpfrontQueueConsumedIsFalse boundary

outboundCitationIsResidual :
  Recursive.outboundCitationsBecomeTypedResiduals boundary ≡ true
outboundCitationIsResidual =
  Recursive.outboundCitationsBecomeTypedResidualsIsTrue boundary

researchRankIsNotTruthRank :
  Recursive.researchPriorityIsLegalTruthRank boundary ≡ false
researchRankIsNotTruthRank =
  Recursive.researchPriorityIsLegalTruthRankIsFalse boundary

identityReviewRemainsExplicit :
  Recursive.authorityIdentityRequiresExplicitReview boundary ≡ true
identityReviewRemainsExplicit =
  Recursive.authorityIdentityRequiresExplicitReviewIsTrue boundary

treatmentReviewRemainsExplicit :
  Recursive.treatmentRequiresExplicitReview boundary ≡ true
treatmentReviewRemainsExplicit =
  Recursive.treatmentRequiresExplicitReviewIsTrue boundary

controllerIsBounded :
  Recursive.recursiveLoopIsBudgetBounded boundary ≡ true
controllerIsBounded =
  Recursive.recursiveLoopIsBudgetBoundedIsTrue boundary

nextAuthorityNeedsNoCaseModule :
  Recursive.caseSpecificCampaignModuleRequiredForNextAuthority boundary ≡ false
nextAuthorityNeedsNoCaseModule =
  Recursive.caseSpecificCampaignModuleRequiredForNextAuthorityIsFalse boundary

waltonsShellStopsOwningContinuation :
  Recursive.waltonsSpecificOrchestrationRequiredAfterCompletedWaltonsHop boundary
    ≡ false
waltonsShellStopsOwningContinuation =
  Recursive.waltonsSpecificOrchestrationRequiredAfterCompletedWaltonsHopIsFalse boundary

controllerCreatesNoAuthority :
  Recursive.campaignCreatesLegalAuthority boundary ≡ false
controllerCreatesNoAuthority =
  Recursive.campaignCreatesLegalAuthorityIsFalse boundary

controllerCreatesNoCurrentLaw :
  Recursive.campaignCreatesCurrentLawConclusion boundary ≡ false
controllerCreatesNoCurrentLaw =
  Recursive.campaignCreatesCurrentLawConclusionIsFalse boundary

capstone :
  Recursive.RecursiveGiumelliCapstoneContract
capstone =
  Recursive.giumelliRecursiveCapstoneContract

giumelliIsFresh :
  Recursive.selectedAuthorityWasAlreadyRepresented capstone ≡ false
giumelliIsFresh =
  Recursive.selectedAuthorityWasAlreadyRepresentedIsFalse capstone

giumelliComesFromObservedCitationResidual :
  Recursive.selectionCameFromOutboundCitationResidual capstone ≡ true
giumelliComesFromObservedCitationResidual =
  Recursive.selectionCameFromOutboundCitationResidualIsTrue capstone

giumelliNeedsNoSpecialRuntime :
  Recursive.caseSpecificRuntimeAdded capstone ≡ false
giumelliNeedsNoSpecialRuntime =
  Recursive.caseSpecificRuntimeAddedIsFalse capstone

capstoneDoesNotFakeLiveReceipt :
  Recursive.claimsLiveSecondHopReceiptAlreadyObserved capstone ≡ false
capstoneDoesNotFakeLiveReceipt =
  Recursive.claimsLiveSecondHopReceiptAlreadyObservedIsFalse capstone
