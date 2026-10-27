{-# OPTIONS --safe #-}
module DASHI.Unified.NavierStokesClayFrontierTOEConvergenceExact where

------------------------------------------------------------------------
-- NAVIER-STOKES CLAY FRONTIER / TOE CONVERGENCE
--
-- O. Objective.
-- Reuse the current canonical Navier-Stokes A/B/C/D max-cut, canonical Clay
-- residual scheduler, final Clay-distance receipt, and authority guard in the
-- focused DASHI TOE graph.
--
-- R. Reuse.
-- NSABCDMaxCut20261007Exact owns the irreducible A/B/C/D programme split.
-- NSCanonicalClayResidualExact owns the canonical typed residual scheduler.
-- NSClayDistanceFinalReceipt owns the later carrier-to-general structural gap.
-- NSAuthorityConsistencyGuard owns the mixed-scope promotion guard.
--
-- C. Construction.
-- This module exports exact aliases and non-promotion theorems only.
-- It adds no Navier-Stokes estimate and no new Clay theorem.
--
-- S. Scope.
-- A/B remain internal theorem-development lanes.
-- C/D remain released-proof audit lanes.
-- Carrier-structured completion does not imply general NS completion.
-- No closed finite or modeled result promotes the Clay target.
--
-- L. Lane.
-- One NS-frontier-to-TOE normalization lane.
-- No ESD or digital_esd surface is edited.
--
-- P. Postcondition.
-- The focused TOE graph reaches the authoritative A/B/C/D cut, canonical
-- residual scheduler, structural gap, and exact non-promotion theorems.
--
-- G. Governance.
-- Original mathematical authors and existing DASHI theorem owners retain
-- authority.  This file owns normalization only.
-- Meta-introspector repositories retain separate attribution and authority.
--
-- F. Verification.
-- Validation must prove definitional agreement with every reused owner.
-- Kernel-green status requires an exact-head Agda/CI receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSABCDMaxCut20261007Exact as ABCD
import DASHI.Physics.Closure.NSCanonicalClayResidualExact as Canonical
import DASHI.Physics.Closure.NSClayDistanceFinalReceipt as Distance
import DASHI.Physics.Closure.NSAuthorityConsistencyGuard as Guard
import DASHI.Physics.Closure.ClayNSProofRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.NSClaySubmissionEligibilityRoadmapReceipt as Eligibility
import DASHI.Physics.Closure.NSTriadKNR650CurrentSharedWeightedWallRound736Exact as R736

open Distance public using (NSClayDistanceFinalPromotion)

------------------------------------------------------------------------
-- Exact reused frontier state.
------------------------------------------------------------------------

navierStokesABCDClayPromotion : Bool
navierStokesABCDClayPromotion =
  ABCD.clayPromotion

navierStokesABCDClayPromotionStillFalse :
  navierStokesABCDClayPromotion ≡ false
navierStokesABCDClayPromotionStillFalse =
  ABCD.clayPromotionIsFalse

canonicalSchedulerClayPromotion : Bool
canonicalSchedulerClayPromotion =
  Canonical.clayPromotion

canonicalSchedulerClayPromotionStillFalse :
  canonicalSchedulerClayPromotion ≡ false
canonicalSchedulerClayPromotionStillFalse =
  Canonical.clayPromotionIsFalse

canonicalSchedulerNavierStokesPromoted : Bool
canonicalSchedulerNavierStokesPromoted =
  Canonical.clayNavierStokesPromoted

canonicalSchedulerNavierStokesStillNotPromoted :
  canonicalSchedulerNavierStokesPromoted ≡ false
canonicalSchedulerNavierStokesStillNotPromoted =
  Canonical.clayNavierStokesPromotedIsFalse

unresolvedHistoricalPackagesDischarged : Bool
unresolvedHistoricalPackagesDischarged =
  Canonical.unresolvedPackagesDischarged

unresolvedHistoricalPackagesStillNotDischarged :
  unresolvedHistoricalPackagesDischarged ≡ false
unresolvedHistoricalPackagesStillNotDischarged =
  Canonical.unresolvedPackagesDischargedIsFalse

------------------------------------------------------------------------
-- Final structural gap and direct non-promotion theorem.
------------------------------------------------------------------------

navierStokesClayDistanceReceipt :
  Distance.NSClayDistanceFinalReceipt
navierStokesClayDistanceReceipt =
  Distance.canonicalNSClayDistanceFinalReceipt

generalNSGlobalRegularityComplete : Bool
generalNSGlobalRegularityComplete =
  Distance.generalNSGlobalRegularityComplete
    navierStokesClayDistanceReceipt

generalNSGlobalRegularityStillOpen :
  generalNSGlobalRegularityComplete ≡ false
generalNSGlobalRegularityStillOpen =
  Distance.generalNSGlobalRegularityCompleteIsFalseHere
    navierStokesClayDistanceReceipt

carrierToGeneralNSImplicationProved : Bool
carrierToGeneralNSImplicationProved =
  Distance.carrierToGeneralNSImplicationProved
    navierStokesClayDistanceReceipt

carrierToGeneralNSImplicationStillOpen :
  carrierToGeneralNSImplicationProved ≡ false
carrierToGeneralNSImplicationStillOpen =
  Distance.carrierToGeneralNSImplicationProvedIsFalseHere
    navierStokesClayDistanceReceipt

terminalClayPromotionImpossible :
  Distance.NSClayDistanceFinalPromotion → ⊥
terminalClayPromotionImpossible =
  Distance.nsClayDistanceFinalPromotionImpossibleHere

------------------------------------------------------------------------
-- Mixed-scope authority guard.
------------------------------------------------------------------------

navierStokesAuthorityGuard :
  Guard.NSAuthorityConsistencyGuard
navierStokesAuthorityGuard =
  Guard.canonicalNSAuthorityConsistencyGuard

navierStokesPromotionGuard : Bool
navierStokesPromotionGuard =
  Guard.canonicalNSPromotionGuard

navierStokesPromotionGuardStillFalse :
  navierStokesPromotionGuard ≡ false
navierStokesPromotionGuardStillFalse =
  Guard.canonicalNSPromotionGuardIsFalse

------------------------------------------------------------------------
-- Current released C/D audit receipts.
------------------------------------------------------------------------

releasedCSourceAuditClosed : Bool
releasedCSourceAuditClosed =
  ABCD.releasedCSourceAuditClosed

releasedDSourceAuditClosed : Bool
releasedDSourceAuditClosed =
  ABCD.releasedDSourceAuditClosed

releasedCHeadStatementStable : Bool
releasedCHeadStatementStable =
  ABCD.cCurrentReleasedHeadStatementStable

releasedDHeadStatementStable : Bool
releasedDHeadStatementStable =
  ABCD.dCurrentReleasedHeadStatementStable

releasedCHeadStatementStableIsTrue :
  releasedCHeadStatementStable ≡ true
releasedCHeadStatementStableIsTrue =
  ABCD.cCurrentReleasedHeadStatementStableIsTrue

releasedDHeadStatementStableIsTrue :
  releasedDHeadStatementStable ≡ true
releasedDHeadStatementStableIsTrue =
  ABCD.dCurrentReleasedHeadStatementStableIsTrue

releasedHeadRequiresReopeningCoordinateAudit : Bool
releasedHeadRequiresReopeningCoordinateAudit =
  ABCD.cdCurrentHeadRequiresReopeningCoordinateAudit

releasedHeadDoesNotRequireReopeningCoordinateAudit :
  releasedHeadRequiresReopeningCoordinateAudit ≡ false
releasedHeadDoesNotRequireReopeningCoordinateAudit =
  ABCD.cdCurrentHeadRequiresReopeningCoordinateAuditIsFalse


------------------------------------------------------------------------
-- Current periodic-B shared weighted wall.
--
-- R736 is the preferred current periodic analytic max-cut.
-- It supersedes older producer-coordinate cuts without changing theorem
-- ownership or promotion status.
------------------------------------------------------------------------

currentSharedWeightedLeafCount = R736.currentSharedWeightedLeafCount

currentSharedWeightedExactlyTwoLeaves : Bool
currentSharedWeightedExactlyTwoLeaves =
  R736.round736ExactlyTwoPreferredAnalyticLeaves

currentSharedWeightedExactlyTwoLeavesIsTrue :
  currentSharedWeightedExactlyTwoLeaves ≡ true
currentSharedWeightedExactlyTwoLeavesIsTrue =
  R736.round736ExactlyTwoPreferredAnalyticLeavesIsTrue

currentSharedWeightedSameCarrier : Bool
currentSharedWeightedSameCarrier =
  R736.round736BothLeavesUseSameWeightedCarrier

currentSharedWeightedSameCarrierIsTrue :
  currentSharedWeightedSameCarrier ≡ true
currentSharedWeightedSameCarrierIsTrue =
  R736.round736BothLeavesUseSameWeightedCarrierIsTrue

currentSharedWeightedCarrierIsInputLaplacian : Bool
currentSharedWeightedCarrierIsInputLaplacian =
  R736.round736WeightedCarrierIsInputLaplacianWork

currentSharedWeightedCarrierIsInputLaplacianIsTrue :
  currentSharedWeightedCarrierIsInputLaplacian ≡ true
currentSharedWeightedCarrierIsInputLaplacianIsTrue =
  R736.round736WeightedCarrierIsInputLaplacianWorkIsTrue

currentWeightedPlusEndpointClosed : Bool
currentWeightedPlusEndpointClosed =
  R736.round736WeightedPlusEndpointClosed

currentWeightedPlusEndpointStillOpen :
  currentWeightedPlusEndpointClosed ≡ false
currentWeightedPlusEndpointStillOpen =
  R736.round736WeightedPlusEndpointClosedIsFalse

currentAugmentedCriticalWeightedClosed : Bool
currentAugmentedCriticalWeightedClosed =
  R736.round736AugmentedCriticalWeightedClosed

currentAugmentedCriticalWeightedStillOpen :
  currentAugmentedCriticalWeightedClosed ≡ false
currentAugmentedCriticalWeightedStillOpen =
  R736.round736AugmentedCriticalWeightedClosedIsFalse

currentSharedWeightedLeavesBuildBarrier : Bool
currentSharedWeightedLeavesBuildBarrier =
  R736.round736TwoLeavesBuildCriticalBarrier

currentSharedWeightedLeavesBuildBarrierIsTrue :
  currentSharedWeightedLeavesBuildBarrier ≡ true
currentSharedWeightedLeavesBuildBarrierIsTrue =
  R736.round736TwoLeavesBuildCriticalBarrierIsTrue

legacyR726IndependentLeafRequired : Bool
legacyR726IndependentLeafRequired =
  R736.round736R726IndependentLeafRequired

legacyR726IndependentLeafNotRequired :
  legacyR726IndependentLeafRequired ≡ false
legacyR726IndependentLeafNotRequired =
  R736.round736R726IndependentLeafRequiredIsFalse

legacyStrictMarginR406IndependentLeafRequired : Bool
legacyStrictMarginR406IndependentLeafRequired =
  R736.round736StrictMarginR406IndependentLeafRequired

legacyStrictMarginR406IndependentLeafNotRequired :
  legacyStrictMarginR406IndependentLeafRequired ≡ false
legacyStrictMarginR406IndependentLeafNotRequired =
  R736.round736StrictMarginR406IndependentLeafRequiredIsFalse

barrierDependentQPlusMinusShortcutAdmissible : Bool
barrierDependentQPlusMinusShortcutAdmissible =
  R736.round736BarrierDependentQPlusMinusShortcutAdmissible

barrierDependentQPlusMinusShortcutStillCircular :
  barrierDependentQPlusMinusShortcutAdmissible ≡ false
barrierDependentQPlusMinusShortcutStillCircular =
  R736.round736BarrierDependentQPlusMinusShortcutAdmissibleIsFalse

currentSharedWeightedClayPromotion : Bool
currentSharedWeightedClayPromotion =
  R736.round736ClayPromotion

currentSharedWeightedClayPromotionStillFalse :
  currentSharedWeightedClayPromotion ≡ false
currentSharedWeightedClayPromotionStillFalse =
  R736.round736ClayPromotionIsFalse

------------------------------------------------------------------------
-- Canonical roadmap and submission-eligibility reconciliation.
------------------------------------------------------------------------

navierStokesRoadmapReceipt :
  Roadmap.ClayNSProofRoadmapReceipt
navierStokesRoadmapReceipt =
  Roadmap.canonicalClayNSProofRoadmapReceipt

navierStokesRoadmapClayStillFalse :
  Roadmap.clayNavierStokesPromoted navierStokesRoadmapReceipt ≡ false
navierStokesRoadmapClayStillFalse =
  Roadmap.clayNSRoadmapKeepsClayFalse

navierStokesRoadmapTerminalStillFalse :
  Roadmap.terminalClaimPromoted navierStokesRoadmapReceipt ≡ false
navierStokesRoadmapTerminalStillFalse =
  Roadmap.clayNSRoadmapKeepsTerminalFalse

navierStokesSubmissionEligibilityReceipt :
  Eligibility.NSClaySubmissionEligibilityRoadmapReceipt
navierStokesSubmissionEligibilityReceipt =
  Eligibility.canonicalNSClaySubmissionEligibilityRoadmapReceipt

continuumBKMPassageConstructed : Bool
continuumBKMPassageConstructed =
  Eligibility.continuumBKMPassageConstructed
    navierStokesSubmissionEligibilityReceipt

continuumBKMPassageStillOpen :
  continuumBKMPassageConstructed ≡ false
continuumBKMPassageStillOpen =
  Eligibility.continuumBKMPassageConstructedIsFalse
    navierStokesSubmissionEligibilityReceipt

allDataBridgeConstructed : Bool
allDataBridgeConstructed =
  Eligibility.allDataBridgeConstructed
    navierStokesSubmissionEligibilityReceipt

allDataBridgeStillOpen :
  allDataBridgeConstructed ≡ false
allDataBridgeStillOpen =
  Eligibility.allDataBridgeConstructedIsFalse
    navierStokesSubmissionEligibilityReceipt

submissionPacketReady : Bool
submissionPacketReady =
  Eligibility.submissionPacketReady
    navierStokesSubmissionEligibilityReceipt

submissionPacketStillNotReady :
  submissionPacketReady ≡ false
submissionPacketStillNotReady =
  Eligibility.submissionPacketReadyIsFalse
    navierStokesSubmissionEligibilityReceipt

clayEligible : Bool
clayEligible =
  Eligibility.clayEligible
    navierStokesSubmissionEligibilityReceipt

clayEligibilityStillFalse :
  clayEligible ≡ false
clayEligibilityStillFalse =
  Eligibility.clayEligibleIsFalse
    navierStokesSubmissionEligibilityReceipt

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F process frame.
------------------------------------------------------------------------

record NavierStokesClayFrontierTOEZKPFrame : Set where
  field
    objective : String
    reuseRule : String
    constructionRule : String
    scopeRule : String
    laneRule : String
    preconditionRule : String
    invariantRule : String
    postconditionRule : String
    governanceRule : String
    verificationRule : String

    ownersExist : Bool
    ownersExistIsTrue : ownersExist ≡ true

    noNewPDETheorem : Bool
    noNewPDETheoremIsTrue : noNewPDETheorem ≡ true

    exactNonPromotionReachable : Bool
    exactNonPromotionReachableIsTrue : exactNonPromotionReachable ≡ true

    clayPromotionBlocked : Bool
    clayPromotionBlockedIsFalse : clayPromotionBlocked ≡ false

open NavierStokesClayFrontierTOEZKPFrame public

canonicalNavierStokesClayFrontierTOEZKPFrame :
  NavierStokesClayFrontierTOEZKPFrame
canonicalNavierStokesClayFrontierTOEZKPFrame =
  record
    { objective =
        "Normalize the canonical Navier-Stokes Clay frontier and exact non-promotion theorems into the DASHI TOE graph."
    ; reuseRule =
        "Reuse the A/B/C/D max-cut, R736 shared weighted wall, canonical residual scheduler, final Clay-distance receipt, and authority guard before adding any adapter."
    ; constructionRule =
        "Expose exact owner aliases and theorem-level non-promotion only."
    ; scopeRule =
        "Treat R736 as the preferred periodic-B analytic max-cut. Keep its two weighted leaves open. Keep A/B internal theorem development separate from released C/D audit and from carrier-structured completion."
    ; laneRule =
        "Use one Navier-Stokes normalization lane and keep ESD surfaces unchanged."
    ; preconditionRule =
        "Require the canonical R736 owner, A/B/C/D max-cut, residual scheduler, Clay-distance receipt, authority guard, roadmap, and submission-eligibility owners to exist before normalization."
    ; invariantRule =
        "Preserve theorem ownership. Preserve exactly two preferred R736 analytic leaves. Preserve the shared weighted/input-Laplacian carrier. Do not promote producer strategies, circular Q-plus-minus shortcuts, finite carriers, or released C/D audit facts into a Clay proof."
    ; postconditionRule =
        "Expose the R736 shared wall, both open leaves, barrier compiler, structural gap, and exact false promotion gates through TOE, Unifier, and Unified.Physics."
    ; governanceRule =
        "Preserve theorem ownership, source attribution, A/B/C/D lane separation, and failure-closed promotion."
    ; verificationRule =
        "Require focused definitional validation and an exact-head Agda/CI receipt before kernel-green claims."
    ; ownersExist = true
    ; ownersExistIsTrue = refl
    ; noNewPDETheorem = true
    ; noNewPDETheoremIsTrue = refl
    ; exactNonPromotionReachable = true
    ; exactNonPromotionReachableIsTrue = refl
    ; clayPromotionBlocked = navierStokesABCDClayPromotion
    ; clayPromotionBlockedIsFalse =
        navierStokesABCDClayPromotionStillFalse
    }
