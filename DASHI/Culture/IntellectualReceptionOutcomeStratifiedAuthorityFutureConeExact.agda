module DASHI.Culture.IntellectualReceptionOutcomeStratifiedAuthorityFutureConeExact where

open import DASHI.Core.Prelude

import DASHI.Culture.IntellectualReceptionContextIndexedAuthorisedStabiliserProofSearchExperimentExact as Context
import DASHI.Culture.IntellectualReceptionContextAuthorisationSequentialExperimentExact as Sequential
import DASHI.Culture.IntellectualReceptionStratifiedStabiliserSearchAuthorityFibreExact as Stratified
import DASHI.Culture.IntellectualReceptionSemanticStabiliserParetoAuthorityCrossPollinationExact as Stabiliser
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact as Loop
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchDynamicsExact as Dynamics

------------------------------------------------------------------------
-- OUTCOME-STRATIFIED AUTHORITY FUTURE CONE
--
-- The pending stabiliser fibre does not have one unconditional successor.
-- The authority-status experiment produces an outcome-indexed continuation.
-- Missing authority keeps the semantic candidate investigable but governance-
-- blocked; present authority opens the reviewed/eligible continuation.
--
-- This is prospective branching from the current fine state, not a rewrite of
-- the arrival history that produced that state.
------------------------------------------------------------------------

data AuthorityOutcomeBranch : Set where
  authorityMissingBranch
  authorityPresentBranch
  : AuthorityOutcomeBranch

outcomeBranch : Context.StabiliserExperimentValue → AuthorityOutcomeBranch
outcomeBranch Context.semanticLawfulValue = authorityMissingBranch
outcomeBranch Context.authorityMissingValue = authorityMissingBranch
outcomeBranch Context.authorityPresentValue = authorityPresentBranch

data OutcomeContinuationState : AuthorityOutcomeBranch → Set where
  pendingSearchContinuation :
    OutcomeContinuationState authorityMissingBranch
  reviewedEligibleContinuation :
    Context.ContextAuthorisedGenerator
      Context.reviewedComparisonContext
      Stabiliser.comparisonFlipXGenerator →
    OutcomeContinuationState authorityPresentBranch

baselineOutcomeContinuation :
  OutcomeContinuationState authorityMissingBranch
baselineOutcomeContinuation = pendingSearchContinuation

reviewedOutcomeContinuation :
  OutcomeContinuationState authorityPresentBranch
reviewedOutcomeContinuation =
  reviewedEligibleContinuation Context.reviewedComparisonReflectionAuthorised

------------------------------------------------------------------------
-- The branch determines the continuation cone, but not by erasing the current
-- stratified state.  Both outcomes start from the same pending semantic/search
-- fibre and differ only in the newly observed authority residual.
------------------------------------------------------------------------

data OutcomeFutureCone : Set where
  reopenSearchCone
  eligibleActionCone
  : OutcomeFutureCone

branchFutureCone : AuthorityOutcomeBranch → OutcomeFutureCone
branchFutureCone authorityMissingBranch = reopenSearchCone
branchFutureCone authorityPresentBranch = eligibleActionCone

futureConesDifferByOutcome :
  branchFutureCone authorityMissingBranch
  ≡ branchFutureCone authorityPresentBranch → ⊥
futureConesDifferByOutcome ()

pendingFineStateIsCommonOrigin : Stratified.StabiliserFineState
pendingFineStateIsCommonOrigin = Stratified.baselineReflectionFibre

missingOutcomeReturnsPendingFineState : Stratified.StabiliserFineState
missingOutcomeReturnsPendingFineState = Stratified.baselineReflectionFibre

presentOutcomeOpensReviewedFineState : Stratified.StabiliserFineState
presentOutcomeOpensReviewedFineState = Stratified.reviewedReflectionFibre

missingOutcomePreservesSemanticStratum :
  Stratified.coarseSemanticStratum missingOutcomeReturnsPendingFineState
  ≡ Stratified.coarseSemanticStratum pendingFineStateIsCommonOrigin
missingOutcomePreservesSemanticStratum = refl

presentOutcomePreservesSemanticStratum :
  Stratified.coarseSemanticStratum presentOutcomeOpensReviewedFineState
  ≡ Stratified.coarseSemanticStratum pendingFineStateIsCommonOrigin
presentOutcomePreservesSemanticStratum = refl

------------------------------------------------------------------------
-- Missing authority loops back into live investigation.  It does not refute the
-- semantic candidate.  Present authority opens the eligible/ranking cone, but
-- only because the independent reviewed authority receipt is supplied.
------------------------------------------------------------------------

missingOutcomeKeepsProofSearchLive : ProofSearch.LiveProofSearch
missingOutcomeKeepsProofSearchLive = Context.comparisonReflectionInvestigationIsLive

missingOutcomeStillBlocksGovernance :
  Context.ContextAuthorisedGenerator
    Context.baselineAuthorityContext
    Stabiliser.comparisonFlipXGenerator → ⊥
missingOutcomeStillBlocksGovernance =
  Context.baselineComparisonReflectionNotAuthorised

presentOutcomeOpensGovernance :
  Context.ContextAuthorisedGenerator
    Context.reviewedComparisonContext
    Stabiliser.comparisonFlipXGenerator
presentOutcomeOpensGovernance =
  Context.reviewedComparisonReflectionAuthorised

presentOutcomeOpensEligibility :
  MDL.Eligible
    (Context.contextEligibilityProblem Context.reviewedComparisonContext)
    Stabiliser.comparisonFlipXGenerator
presentOutcomeOpensEligibility = Context.reviewedComparisonReflectionEligible

------------------------------------------------------------------------
-- Exact link to the existing one-step sequential experiment.  Both concrete
-- outcomes are live, and each refined fibre closes the declared authority
-- consumer.  Closure of that consumer is weaker than whole-context identity.
------------------------------------------------------------------------

missingOutcomeIsLive :
  Planner.OutcomePossible
    Sequential.allAuthorityContextsLive
    Context.authorityStatusBundle
    Context.authorityMissingValue
missingOutcomeIsLive = Sequential.baselineOutcomePossible

presentOutcomeIsLive :
  Planner.OutcomePossible
    Sequential.allAuthorityContextsLive
    Context.authorityStatusBundle
    Context.authorityPresentValue
presentOutcomeIsLive = Sequential.reviewedOutcomePossible

missingOutcomeConsumerCloses :
  Planner.SequentialConsumerPlan
    Context.reflectionAuthorityDecision
    (Planner.RefineByBundle
      Sequential.allAuthorityContextsLive
      Context.authorityStatusBundle
      Context.authorityMissingValue)
missingOutcomeConsumerCloses = Sequential.baselineOutcomeClosesBlockedDecision

presentOutcomeConsumerCloses :
  Planner.SequentialConsumerPlan
    Context.reflectionAuthorityDecision
    (Planner.RefineByBundle
      Sequential.allAuthorityContextsLive
      Context.authorityStatusBundle
      Context.authorityPresentValue)
presentOutcomeConsumerCloses = Sequential.reviewedOutcomeClosesAuthorisedDecision

------------------------------------------------------------------------
-- Active-search dynamics precedent: refined fibres may either close a declared
-- consumer or re-enter live search after reopening.  Here a missing-authority
-- observation closes the authority-status question as "blocked", while the
-- larger semantic programme may remain live and choose another probe.
------------------------------------------------------------------------

activeSearchCanCycleAfterReopening :
  Dynamics.LoopPath Loop.liveHypotheses Loop.liveHypotheses
activeSearchCanCycleAfterReopening = Dynamics.canonicalOneIterationCycle

activeSearchCanCloseConsumer :
  Dynamics.LoopPath Loop.liveHypotheses Loop.consumerClosed
activeSearchCanCloseConsumer = Dynamics.canonicalClosurePath

------------------------------------------------------------------------
-- Boundary: an observed missing receipt is not evidence that the semantic
-- generator is false; an observed present receipt does not backfill historical
-- authority into earlier contexts.
------------------------------------------------------------------------

data MissingAuthorityRefutesSemanticCandidate : Set where
data PresentAuthorityRetroactivelyAuthorisesBaseline : Set where
data OutcomeBranchRewritesArrivalHistory : Set where
data ConsumerClosureEndsAllFutureSearch : Set where

missingAuthorityDoesNotRefuteSemanticCandidate :
  MissingAuthorityRefutesSemanticCandidate → ⊥
missingAuthorityDoesNotRefuteSemanticCandidate ()

presentAuthorityDoesNotRetroactivelyAuthoriseBaseline :
  PresentAuthorityRetroactivelyAuthorisesBaseline → ⊥
presentAuthorityDoesNotRetroactivelyAuthoriseBaseline ()

outcomeBranchDoesNotRewriteArrivalHistory :
  OutcomeBranchRewritesArrivalHistory → ⊥
outcomeBranchDoesNotRewriteArrivalHistory ()

consumerClosureDoesNotEndAllFutureSearch :
  ConsumerClosureEndsAllFutureSearch → ⊥
consumerClosureDoesNotEndAllFutureSearch ()

record IntellectualReceptionOutcomeStratifiedAuthorityFutureConeBoundary : Set where
  constructor intellectual-reception-outcome-stratified-authority-future-cone-boundary
  field
    pendingFibreHasOutcomeIndexedContinuation : Bool
    missingAuthorityMayReopenOrContinueSearch : Bool
    presentAuthorityMayOpenEligibleActionCone : Bool
    missingAuthorityRefutesSemanticLawfulness : Bool
    presentAuthorityRetroactivelyAuthorisesBaseline : Bool
    outcomeBranchRewritesPastHistory : Bool
    consumerClosureMeansAllSearchTerminates : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionOutcomeStratifiedAuthorityFutureConeBoundary :
  IntellectualReceptionOutcomeStratifiedAuthorityFutureConeBoundary
canonicalIntellectualReceptionOutcomeStratifiedAuthorityFutureConeBoundary =
  intellectual-reception-outcome-stratified-authority-future-cone-boundary
    true true true false false false false true
