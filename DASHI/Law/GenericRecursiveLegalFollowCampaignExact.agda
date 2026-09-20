module DASHI.Law.GenericRecursiveLegalFollowCampaignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)

import DASHI.Law.AustralianContractsLandscapeControllerExact as Landscape
import DASHI.Law.AustralianContractsReviewedHopCompilerExact as Reviewed
import DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballExact as OALC
import DASHI.Law.SensibLawNativeLegalFollowCLIExact as CLI

recursiveNativeCommandSurface : List CLI.NativeLegalFollowCommand
recursiveNativeCommandSurface =
  CLI.discoverRecursiveContractFrontier
    ∷ CLI.acquireRecursiveContractAuthority
    ∷ CLI.prepareRecursiveContractIdentityReview
    ∷ CLI.compileRecursiveContractIdentityReview
    ∷ CLI.prepareRecursiveContractTreatmentReview
    ∷ CLI.compileRecursiveContractTreatmentReview
    ∷ []

------------------------------------------------------------------------
-- S14.5 / PHASE IV: GENERIC RECURSIVE LEGALFOLLOW CAMPAIGN
--
-- This owner begins after a root campaign has produced a typed adaptive trace.
-- It persists that typed world, exposes newly observed citation residuals,
-- selects bounded research work, reacquires primary sources, stops at explicit
-- identity/treatment review gates, compiles reviewed hops, and recomputes.
--
-- Selection priority is research scheduling only.  It is never legal truth,
-- authority, treatment or a current-law conclusion.
------------------------------------------------------------------------

data RecursiveFrontierClass : Set where
  primarySourceFrontier : RecursiveFrontierClass
  treatmentReviewFrontier : RecursiveFrontierClass
  contextExpansionFrontier : RecursiveFrontierClass
  temporalAlternativeFrontier : RecursiveFrontierClass
  outboundCitationFrontier : RecursiveFrontierClass

data RecursiveCampaignGate : Set where
  primarySourceAcquisitionGate : RecursiveCampaignGate
  authorityIdentityReviewGate : RecursiveCampaignGate
  treatmentReviewGate : RecursiveCampaignGate
  contextExpansionGate : RecursiveCampaignGate
  temporalAlternativeGate : RecursiveCampaignGate
  budgetExhaustedGate : RecursiveCampaignGate
  noRecursiveGate : RecursiveCampaignGate

record RecursiveCampaignBudget : Set where
  constructor recursiveCampaignBudget
  field
    maximumAcceptedHops : Nat
    maximumSourceAcquisitions : Nat
    maximumNetworkRequests : Nat

open RecursiveCampaignBudget public

canonicalRecursiveCampaignBudget : RecursiveCampaignBudget
canonicalRecursiveCampaignBudget =
  recursiveCampaignBudget 128 32 128

record RecursiveCitationResidual : Set where
  constructor recursiveCitationResidual
  field
    residualReference : String
    sourceDocumentReference : String
    sourceSemanticReference : String
    sourceRevisionReference : String
    canonicalTextDigest : String
    mediumNeutralCitation : String
    citationLocatorReferences : List String
    anchorParagraphLocatorReferences : List String
    researchPriority : Nat
    priorityIsLegalTruthRank : Bool
    priorityIsLegalTruthRankIsFalse :
      priorityIsLegalTruthRank ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse :
      createsLegalAuthority ≡ false
    createsCurrentLawConclusion : Bool
    createsCurrentLawConclusionIsFalse :
      createsCurrentLawConclusion ≡ false

open RecursiveCitationResidual public

record RecursiveCampaignStep : Set where
  constructor recursiveCampaignStep
  field
    gate : RecursiveCampaignGate
    selectedFrontierReference : Maybe String
    selectorIsLegalTruthRank : Bool
    selectorIsLegalTruthRankIsFalse :
      selectorIsLegalTruthRank ≡ false
    boundedByCampaignBudget : Bool
    boundedByCampaignBudgetIsTrue :
      boundedByCampaignBudget ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse :
      createsLegalAuthority ≡ false
    createsCurrentLawConclusion : Bool
    createsCurrentLawConclusionIsFalse :
      createsCurrentLawConclusion ≡ false

open RecursiveCampaignStep public

record GenericRecursiveCampaignBoundary : Set where
  constructor genericRecursiveCampaignBoundary
  field
    finalTypedTraceIsPersisted : Bool
    finalTypedTraceIsPersistedIsTrue :
      finalTypedTraceIsPersisted ≡ true

    continuationRestoresTypedTrace : Bool
    continuationRestoresTypedTraceIsTrue :
      continuationRestoresTypedTrace ≡ true

    freshFrontierRecomputedAfterAcceptedHop : Bool
    freshFrontierRecomputedAfterAcceptedHopIsTrue :
      freshFrontierRecomputedAfterAcceptedHop ≡ true

    fixedUpfrontQueueConsumed : Bool
    fixedUpfrontQueueConsumedIsFalse :
      fixedUpfrontQueueConsumed ≡ false

    outboundCitationsBecomeTypedResiduals : Bool
    outboundCitationsBecomeTypedResidualsIsTrue :
      outboundCitationsBecomeTypedResiduals ≡ true

    alreadyRepresentedAuthorityIsFilteredFromFreshCitationResiduals : Bool
    alreadyRepresentedAuthorityIsFilteredFromFreshCitationResidualsIsTrue :
      alreadyRepresentedAuthorityIsFilteredFromFreshCitationResiduals ≡ true

    researchPriorityIsLegalTruthRank : Bool
    researchPriorityIsLegalTruthRankIsFalse :
      researchPriorityIsLegalTruthRank ≡ false

    recursiveSourceAcquisitionUsesGovernedOalc : Bool
    recursiveSourceAcquisitionUsesGovernedOalcIsTrue :
      recursiveSourceAcquisitionUsesGovernedOalc ≡ true

    missingRecursiveSourceIsNegativeLegalEvidence : Bool
    missingRecursiveSourceIsNegativeLegalEvidenceIsFalse :
      missingRecursiveSourceIsNegativeLegalEvidence ≡ false

    rawRecursiveSourceCreatesAuthorityIdentity : Bool
    rawRecursiveSourceCreatesAuthorityIdentityIsFalse :
      rawRecursiveSourceCreatesAuthorityIdentity ≡ false

    authorityIdentityRequiresExplicitReview : Bool
    authorityIdentityRequiresExplicitReviewIsTrue :
      authorityIdentityRequiresExplicitReview ≡ true

    citationOccurrenceCreatesTreatment : Bool
    citationOccurrenceCreatesTreatmentIsFalse :
      citationOccurrenceCreatesTreatment ≡ false

    treatmentRequiresExplicitReview : Bool
    treatmentRequiresExplicitReviewIsTrue :
      treatmentRequiresExplicitReview ≡ true

    reviewedIdentityUsesGenericReviewedHopCompiler : Bool
    reviewedIdentityUsesGenericReviewedHopCompilerIsTrue :
      reviewedIdentityUsesGenericReviewedHopCompiler ≡ true

    reviewedTreatmentUsesGenericReviewedHopCompiler : Bool
    reviewedTreatmentUsesGenericReviewedHopCompilerIsTrue :
      reviewedTreatmentUsesGenericReviewedHopCompiler ≡ true

    recursiveLoopIsBudgetBounded : Bool
    recursiveLoopIsBudgetBoundedIsTrue :
      recursiveLoopIsBudgetBounded ≡ true

    parentCampaignReceiptIsPreserved : Bool
    parentCampaignReceiptIsPreservedIsTrue :
      parentCampaignReceiptIsPreserved ≡ true

    continuationMayResetBudgetCounters : Bool
    continuationMayResetBudgetCountersIsFalse :
      continuationMayResetBudgetCounters ≡ false

    governedAcquisitionReservesProviderRequestBound : Bool
    governedAcquisitionReservesProviderRequestBoundIsTrue :
      governedAcquisitionReservesProviderRequestBound ≡ true

    successfulAcquisitionAdvancesCampaignReceipt : Bool
    successfulAcquisitionAdvancesCampaignReceiptIsTrue :
      successfulAcquisitionAdvancesCampaignReceipt ≡ true

    acquisitionPreparesAuthorityIdentityGate : Bool
    acquisitionPreparesAuthorityIdentityGateIsTrue :
      acquisitionPreparesAuthorityIdentityGate ≡ true

    reviewedIdentityPreparesTreatmentGate : Bool
    reviewedIdentityPreparesTreatmentGateIsTrue :
      reviewedIdentityPreparesTreatmentGate ≡ true

    reviewedTreatmentEmitsNextOutboundFrontier : Bool
    reviewedTreatmentEmitsNextOutboundFrontierIsTrue :
      reviewedTreatmentEmitsNextOutboundFrontier ≡ true

    sourceAcquisitionAutomaticallyAddsLegalHop : Bool
    sourceAcquisitionAutomaticallyAddsLegalHopIsFalse :
      sourceAcquisitionAutomaticallyAddsLegalHop ≡ false

    caseSpecificCampaignModuleRequiredForNextAuthority : Bool
    caseSpecificCampaignModuleRequiredForNextAuthorityIsFalse :
      caseSpecificCampaignModuleRequiredForNextAuthority ≡ false

    waltonsSpecificOrchestrationRequiredAfterCompletedWaltonsHop : Bool
    waltonsSpecificOrchestrationRequiredAfterCompletedWaltonsHopIsFalse :
      waltonsSpecificOrchestrationRequiredAfterCompletedWaltonsHop ≡ false

    campaignCreatesLegalAuthority : Bool
    campaignCreatesLegalAuthorityIsFalse :
      campaignCreatesLegalAuthority ≡ false

    campaignCreatesCurrentLawConclusion : Bool
    campaignCreatesCurrentLawConclusionIsFalse :
      campaignCreatesCurrentLawConclusion ≡ false

open GenericRecursiveCampaignBoundary public

canonicalGenericRecursiveCampaignBoundary :
  GenericRecursiveCampaignBoundary
canonicalGenericRecursiveCampaignBoundary =
  genericRecursiveCampaignBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- No-collapse laws for recursive research.
------------------------------------------------------------------------

data ResearchPriorityAutomaticallyLegalTruth : Set where
data OutboundCitationAutomaticallyAuthority : Set where
data OutboundCitationAutomaticallyTreatment : Set where
data MissingRecursiveSourceAutomaticallyNegativeEvidence : Set where
data RawRecursiveSourceAutomaticallyReviewedIdentity : Set where
data RecursiveTreatmentMaySkipReview : Set where
data RecursiveControllerMayFreezeOldConclusion : Set where
data RecursiveControllerMayConsumeFixedQueue : Set where
data RecursiveNextAuthorityRequiresCaseSpecificRuntime : Set where
data RecursiveContinuationMayResetBudget : Set where
data SuccessfulAcquisitionAutomaticallyLegalHop : Set where
data RecursiveCampaignMayDropParentReceipt : Set where
data AcquisitionMaySkipIdentityGate : Set where
data ReviewedIdentityMaySkipTreatmentGate : Set where
data ReviewedTreatmentMayFailToRecomputeOutboundFrontier : Set where

researchPriorityDoesNotBecomeLegalTruth :
  ResearchPriorityAutomaticallyLegalTruth → ⊥
researchPriorityDoesNotBecomeLegalTruth ()

outboundCitationDoesNotCreateAuthority :
  OutboundCitationAutomaticallyAuthority → ⊥
outboundCitationDoesNotCreateAuthority ()

outboundCitationDoesNotCreateTreatment :
  OutboundCitationAutomaticallyTreatment → ⊥
outboundCitationDoesNotCreateTreatment ()

missingRecursiveSourceDoesNotBecomeNegativeEvidence :
  MissingRecursiveSourceAutomaticallyNegativeEvidence → ⊥
missingRecursiveSourceDoesNotBecomeNegativeEvidence ()

rawRecursiveSourceDoesNotBecomeReviewedIdentity :
  RawRecursiveSourceAutomaticallyReviewedIdentity → ⊥
rawRecursiveSourceDoesNotBecomeReviewedIdentity ()

recursiveTreatmentCannotSkipReview :
  RecursiveTreatmentMaySkipReview → ⊥
recursiveTreatmentCannotSkipReview ()

recursiveControllerDoesNotFreezeOldConclusion :
  RecursiveControllerMayFreezeOldConclusion → ⊥
recursiveControllerDoesNotFreezeOldConclusion ()

recursiveControllerDoesNotConsumeFixedQueue :
  RecursiveControllerMayConsumeFixedQueue → ⊥
recursiveControllerDoesNotConsumeFixedQueue ()

recursiveNextAuthorityNeedsNoCaseSpecificRuntime :
  RecursiveNextAuthorityRequiresCaseSpecificRuntime → ⊥
recursiveNextAuthorityNeedsNoCaseSpecificRuntime ()

recursiveContinuationCannotResetBudget :
  RecursiveContinuationMayResetBudget → ⊥
recursiveContinuationCannotResetBudget ()

successfulAcquisitionDoesNotAutomaticallyAddLegalHop :
  SuccessfulAcquisitionAutomaticallyLegalHop → ⊥
successfulAcquisitionDoesNotAutomaticallyAddLegalHop ()

recursiveCampaignCannotDropParentReceipt :
  RecursiveCampaignMayDropParentReceipt → ⊥
recursiveCampaignCannotDropParentReceipt ()

acquisitionCannotSkipIdentityGate :
  AcquisitionMaySkipIdentityGate → ⊥
acquisitionCannotSkipIdentityGate ()

reviewedIdentityCannotSkipTreatmentGate :
  ReviewedIdentityMaySkipTreatmentGate → ⊥
reviewedIdentityCannotSkipTreatmentGate ()

reviewedTreatmentMustRecomputeOutboundFrontier :
  ReviewedTreatmentMayFailToRecomputeOutboundFrontier → ⊥
reviewedTreatmentMustRecomputeOutboundFrontier ()

------------------------------------------------------------------------
-- Phase-IV capstone contract.
--
-- Sidhu is deliberately not the witness here because the pre-existing Waltons
-- trace already represented it.  Giumelli is the clean fresh authority exposed
-- by the retained Doueihi source.  This record is an implementation acceptance
-- contract; it does not claim a live second-hop review receipt has already run.
------------------------------------------------------------------------

record RecursiveGiumelliCapstoneContract : Set where
  constructor recursiveGiumelliCapstoneContract
  field
    completedSourceAuthorityReference : String
    selectedFreshMediumNeutralCitation : String
    selectedAuthorityWasAlreadyRepresented : Bool
    selectedAuthorityWasAlreadyRepresentedIsFalse :
      selectedAuthorityWasAlreadyRepresented ≡ false
    selectionCameFromOutboundCitationResidual : Bool
    selectionCameFromOutboundCitationResidualIsTrue :
      selectionCameFromOutboundCitationResidual ≡ true
    governedOalcReacquisitionIsNextDeterministicAction : Bool
    governedOalcReacquisitionIsNextDeterministicActionIsTrue :
      governedOalcReacquisitionIsNextDeterministicAction ≡ true
    identityReviewGateIsRequired : Bool
    identityReviewGateIsRequiredIsTrue :
      identityReviewGateIsRequired ≡ true
    treatmentReviewGateIsRequired : Bool
    treatmentReviewGateIsRequiredIsTrue :
      treatmentReviewGateIsRequired ≡ true
    reviewedHopFeedsSameTypedTrajectory : Bool
    reviewedHopFeedsSameTypedTrajectoryIsTrue :
      reviewedHopFeedsSameTypedTrajectory ≡ true
    caseSpecificRuntimeAdded : Bool
    caseSpecificRuntimeAddedIsFalse :
      caseSpecificRuntimeAdded ≡ false
    claimsLiveSecondHopReceiptAlreadyObserved : Bool
    claimsLiveSecondHopReceiptAlreadyObservedIsFalse :
      claimsLiveSecondHopReceiptAlreadyObserved ≡ false

open RecursiveGiumelliCapstoneContract public

giumelliRecursiveCapstoneContract :
  RecursiveGiumelliCapstoneContract
giumelliRecursiveCapstoneContract =
  recursiveGiumelliCapstoneContract
    "case:nsw:nswca:2016:105"
    "[1999] HCA 10"
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

LandscapeBoundary : Set
LandscapeBoundary = Landscape.AustralianContractsLandscapeControllerBoundary

landscapeBoundaryPaid : LandscapeBoundary
landscapeBoundaryPaid =
  Landscape.canonicalAustralianContractsLandscapeControllerBoundary

ReviewedBoundary : Set
ReviewedBoundary = Reviewed.AustralianContractsReviewedHopCompilerBoundary

reviewedBoundaryPaid : ReviewedBoundary
reviewedBoundaryPaid =
  Reviewed.canonicalAustralianContractsReviewedHopCompilerBoundary

OalcBoundary : Set
OalcBoundary = OALC.OalcLegalFollowAttributionBoundary

oalcBoundaryPaid : OalcBoundary
oalcBoundaryPaid =
  OALC.canonicalOalcLegalFollowAttributionBoundary