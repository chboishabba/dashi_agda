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
-- NSClayFacingBPureAnalysisFrontier20261005Exact owns the current periodic-B
-- physical R440 wall and keeps R823 frozen.
-- NSHistoricalSignedExternalCommutatorSnowballLineageExact owns the historical
-- signed Waleffe-to-commutator donor lineage and its non-promotion receipts.
-- NSCanonicalClayResidualExact owns the canonical typed residual scheduler.
-- NSClayDistanceFinalReceipt owns the later carrier-to-general structural gap.
-- NSAuthorityConsistencyGuard owns the mixed-scope promotion guard.
-- R736 remains imported for legacy compatibility only.
--
-- C. Construction.
-- This module exports exact aliases and non-promotion theorems only.
-- It adds no Navier-Stokes estimate and no new Clay theorem.
--
-- S. Scope.
-- A/B remain internal theorem-development lanes.
-- The current B highest-information leaf is the literal physical R440 payment.
-- The historical external-commutator chain and R736 are donor surfaces.
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
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSABCDMaxCut20261007Exact as ABCD
import DASHI.Physics.Closure.NSCanonicalClayResidualExact as Canonical
import DASHI.Physics.Closure.NSClayDistanceFinalReceipt as Distance
import DASHI.Physics.Closure.NSAuthorityConsistencyGuard as Guard
import DASHI.Physics.Closure.ClayNSProofRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.NSClaySubmissionEligibilityRoadmapReceipt as Eligibility
import DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Exact as BCurrent
import DASHI.Physics.Closure.NSHistoricalSignedExternalCommutatorSnowballLineageExact as History
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
-- Current periodic-B authoritative wall.
--
-- NSABCDMaxCut20261007Exact routes B to the pure-analysis frontier.
-- That frontier names the literal physical R440 noncore/core payment as the
-- highest-information B leaf.  Representation work is frozen.
--
-- The historical signed external-Waleffe/commutator chain remains a useful
-- donor.  It is not the current preferred B leaf and does not promote Clay.
------------------------------------------------------------------------

currentPeriodicBHighestInformationIsPhysicalR440 : Bool
currentPeriodicBHighestInformationIsPhysicalR440 =
  BCurrent.b4ResearchLeafNowOnlyPhysicalR440Payment

currentPeriodicB4PhysicalPaymentClosed : Bool
currentPeriodicB4PhysicalPaymentClosed =
  BCurrent.b4DefectRemainderClosed

currentPeriodicB4FourMomentScalarClosed : Bool
currentPeriodicB4FourMomentScalarClosed =
  BCurrent.b4DefectR440FourMomentScalarClosed

currentPeriodicB4ZeroPaddingAuditClosed : Bool
currentPeriodicB4ZeroPaddingAuditClosed =
  BCurrent.b4DefectR440ZeroPaddingAuditClosed

currentPeriodicB1PhysicalProducerClosed : Bool
currentPeriodicB1PhysicalProducerClosed =
  BCurrent.b1PhysicalProducerClosed

currentPeriodicB2PhysicalProducerClosed : Bool
currentPeriodicB2PhysicalProducerClosed =
  BCurrent.b2PhysicalProducerClosed

currentPeriodicB3PhysicalProducerClosed : Bool
currentPeriodicB3PhysicalProducerClosed =
  BCurrent.b3PhysicalProducerClosed

currentPeriodicBContinuationInputsClosed : Bool
currentPeriodicBContinuationInputsClosed =
  BCurrent.bContinuationPhysicalInputsClosed

currentPeriodicBRepresentationProgrammeFrozen : Bool
currentPeriodicBRepresentationProgrammeFrozen =
  ABCD.bRepresentationProgrammeFrozen

currentPeriodicBR823ShouldReopen : Bool
currentPeriodicBR823ShouldReopen =
  BCurrent.r823ShouldReopen

historicalExternalSignedCommutatorRouteReachedPureCommutator : Bool
historicalExternalSignedCommutatorRouteReachedPureCommutator =
  History.historicalNestedInnerPureCommutatorExposed

historicalExternalSignedCommutatorModernWeldAddsEstimate : Bool
historicalExternalSignedCommutatorModernWeldAddsEstimate =
  History.modernWeightedNestedWeldIntroducesNewEstimate

historicalExternalSignedCommutatorRoutePromotesClay : Bool
historicalExternalSignedCommutatorRoutePromotesClay =
  History.historicalStructuralLineageAlonePromotesClay

currentPeriodicBHighestInformationIsPhysicalR440IsTrue :
  currentPeriodicBHighestInformationIsPhysicalR440 ≡ true
currentPeriodicBHighestInformationIsPhysicalR440IsTrue =
  BCurrent.b4ResearchLeafNowOnlyPhysicalR440PaymentIsTrue

currentPeriodicB4PhysicalPaymentStillOpen :
  currentPeriodicB4PhysicalPaymentClosed ≡ false
currentPeriodicB4PhysicalPaymentStillOpen =
  BCurrent.b4DefectRemainderClosedIsFalse

currentPeriodicB4FourMomentScalarClosedIsTrue :
  currentPeriodicB4FourMomentScalarClosed ≡ true
currentPeriodicB4FourMomentScalarClosedIsTrue =
  BCurrent.b4DefectR440FourMomentScalarClosedIsTrue

currentPeriodicB4ZeroPaddingAuditClosedIsTrue :
  currentPeriodicB4ZeroPaddingAuditClosed ≡ true
currentPeriodicB4ZeroPaddingAuditClosedIsTrue =
  BCurrent.b4DefectR440ZeroPaddingAuditClosedIsTrue

currentPeriodicB1PhysicalProducerStillOpen :
  currentPeriodicB1PhysicalProducerClosed ≡ false
currentPeriodicB1PhysicalProducerStillOpen =
  BCurrent.b1PhysicalProducerClosedIsFalse

currentPeriodicB2PhysicalProducerStillOpen :
  currentPeriodicB2PhysicalProducerClosed ≡ false
currentPeriodicB2PhysicalProducerStillOpen =
  BCurrent.b2PhysicalProducerClosedIsFalse

currentPeriodicB3PhysicalProducerStillOpen :
  currentPeriodicB3PhysicalProducerClosed ≡ false
currentPeriodicB3PhysicalProducerStillOpen =
  BCurrent.b3PhysicalProducerClosedIsFalse

currentPeriodicBContinuationInputsStillOpen :
  currentPeriodicBContinuationInputsClosed ≡ false
currentPeriodicBContinuationInputsStillOpen =
  BCurrent.bContinuationPhysicalInputsClosedIsFalse

currentPeriodicBRepresentationProgrammeFrozenIsTrue :
  currentPeriodicBRepresentationProgrammeFrozen ≡ true
currentPeriodicBRepresentationProgrammeFrozenIsTrue =
  ABCD.bRepresentationProgrammeFrozenIsTrue

currentPeriodicBR823ShouldNotReopen :
  currentPeriodicBR823ShouldReopen ≡ false
currentPeriodicBR823ShouldNotReopen =
  BCurrent.r823ShouldReopenIsFalse

historicalExternalSignedCommutatorRouteReachedPureCommutatorIsTrue :
  historicalExternalSignedCommutatorRouteReachedPureCommutator ≡ true
historicalExternalSignedCommutatorRouteReachedPureCommutatorIsTrue =
  History.historicalNestedInnerPureCommutatorExposedIsTrue

historicalExternalSignedCommutatorModernWeldAddsNoEstimate :
  historicalExternalSignedCommutatorModernWeldAddsEstimate ≡ false
historicalExternalSignedCommutatorModernWeldAddsNoEstimate =
  History.modernWeightedNestedWeldIntroducesNewEstimateIsFalse

historicalExternalSignedCommutatorRouteDoesNotPromoteClay :
  historicalExternalSignedCommutatorRoutePromotesClay ≡ false
historicalExternalSignedCommutatorRouteDoesNotPromoteClay =
  History.historicalStructuralLineageAlonePromotesClayIsFalse


------------------------------------------------------------------------
-- Legacy R736 compatibility surface.
--
-- R736 remains theorem-bearing historical provenance.  It is not the current
-- authoritative B max-cut after NSABCDMaxCut20261007Exact.
-- It supersedes older producer-coordinate cuts without changing theorem
-- ownership or promotion status.
------------------------------------------------------------------------

currentSharedWeightedLeafCount : Nat
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
        "Reuse the A/B/C/D max-cut and current B pure-analysis owner first. Retain R736 and the signed external-commutator chain as historical donors only. Reuse the canonical residual scheduler, final Clay-distance receipt, and authority guard before adding any adapter."
    ; constructionRule =
        "Expose exact owner aliases and theorem-level non-promotion only."
    ; scopeRule =
        "Treat the literal physical R440 noncore/core payment as the current highest-information periodic-B leaf. Keep B1/B2/B3 physical producers and continuation inputs explicit. Keep R736 and the signed external-commutator route historical. Keep A/B internal theorem development separate from released C/D audit and from carrier-structured completion."
    ; laneRule =
        "Use one Navier-Stokes normalization lane and keep ESD surfaces unchanged."
    ; preconditionRule =
        "Require the authoritative A/B/C/D max-cut, current B pure-analysis owner, historical signed external-commutator lineage, residual scheduler, Clay-distance receipt, authority guard, roadmap, and submission-eligibility owners to exist before normalization."
    ; invariantRule =
        "Preserve theorem ownership. Preserve the literal physical R440 payment as the current highest-information B leaf. Preserve the open B1/B2/B3 producer and continuation leaves. Do not reopen R823. Do not promote the historical Waleffe/commutator chain, R736, producer strategies, finite carriers, or released C/D audit facts into a Clay proof."
    ; postconditionRule =
        "Expose the current literal R440 B wall, open physical B producer leaves, historical donor/non-promotion receipts, structural gap, and exact false promotion gates through TOE, Unifier, and Unified.Physics. Retain the R736 aliases for compatibility only."
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
