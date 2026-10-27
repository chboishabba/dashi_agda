{-# OPTIONS --safe #-}
module DASHI.Unified.NavierStokesClayFrontierTOEConvergenceValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.NavierStokesClayFrontierTOEConvergenceExact as NSClay
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as U
import DASHI.Unified.Physics as Physics

adapterClayPromotionStillFalse :
  NSClay.navierStokesABCDClayPromotion ≡ false
adapterClayPromotionStillFalse =
  NSClay.navierStokesABCDClayPromotionStillFalse

adapterGeneralRegularityStillOpen :
  NSClay.generalNSGlobalRegularityComplete ≡ false
adapterGeneralRegularityStillOpen =
  NSClay.generalNSGlobalRegularityStillOpen

adapterCarrierToGeneralStillOpen :
  NSClay.carrierToGeneralNSImplicationProved ≡ false
adapterCarrierToGeneralStillOpen =
  NSClay.carrierToGeneralNSImplicationStillOpen

adapterAuthorityGuardStillFalse :
  NSClay.navierStokesPromotionGuard ≡ false
adapterAuthorityGuardStillFalse =
  NSClay.navierStokesPromotionGuardStillFalse

adapterTerminalPromotionImpossible :
  NSClay.NSClayDistanceFinalPromotion → ⊥
adapterTerminalPromotionImpossible =
  NSClay.terminalClayPromotionImpossible

toeClayBoundaryMatchesAdapter :
  TOE.toeNavierStokesClayPromotion
  ≡ NSClay.navierStokesABCDClayPromotion
toeClayBoundaryMatchesAdapter = refl

toeGeneralRegularityMatchesAdapter :
  TOE.toeNavierStokesGeneralRegularityComplete
  ≡ NSClay.generalNSGlobalRegularityComplete
toeGeneralRegularityMatchesAdapter = refl

toeCarrierToGeneralMatchesAdapter :
  TOE.toeNavierStokesCarrierToGeneralImplicationProved
  ≡ NSClay.carrierToGeneralNSImplicationProved
toeCarrierToGeneralMatchesAdapter = refl

toeAuthorityGuardMatchesAdapter :
  TOE.toeNavierStokesAuthorityPromotionGuard
  ≡ NSClay.navierStokesPromotionGuard
toeAuthorityGuardMatchesAdapter = refl

toeTerminalPromotionImpossible :
  NSClay.NSClayDistanceFinalPromotion → ⊥
toeTerminalPromotionImpossible =
  TOE.toeNavierStokesTerminalPromotionImpossible

unifierClayBoundaryMatchesAdapter :
  U.unifierNavierStokesClayPromotion
  ≡ NSClay.navierStokesABCDClayPromotion
unifierClayBoundaryMatchesAdapter = refl

unifierGeneralRegularityMatchesAdapter :
  U.unifierNavierStokesGeneralRegularityComplete
  ≡ NSClay.generalNSGlobalRegularityComplete
unifierGeneralRegularityMatchesAdapter = refl

unifierCarrierToGeneralMatchesAdapter :
  U.unifierNavierStokesCarrierToGeneralImplicationProved
  ≡ NSClay.carrierToGeneralNSImplicationProved
unifierCarrierToGeneralMatchesAdapter = refl

unifierAuthorityGuardMatchesAdapter :
  U.unifierNavierStokesAuthorityPromotionGuard
  ≡ NSClay.navierStokesPromotionGuard
unifierAuthorityGuardMatchesAdapter = refl

unifierTerminalPromotionImpossible :
  NSClay.NSClayDistanceFinalPromotion → ⊥
unifierTerminalPromotionImpossible =
  U.unifierNavierStokesTerminalPromotionImpossible

physicsClayBoundaryMatchesAdapter :
  Physics.navierStokesClayPromotion
  ≡ NSClay.navierStokesABCDClayPromotion
physicsClayBoundaryMatchesAdapter = refl

physicsGeneralRegularityMatchesAdapter :
  Physics.navierStokesGeneralRegularityComplete
  ≡ NSClay.generalNSGlobalRegularityComplete
physicsGeneralRegularityMatchesAdapter = refl

physicsCarrierToGeneralMatchesAdapter :
  Physics.navierStokesCarrierToGeneralImplicationProved
  ≡ NSClay.carrierToGeneralNSImplicationProved
physicsCarrierToGeneralMatchesAdapter = refl

physicsAuthorityGuardMatchesAdapter :
  Physics.navierStokesAuthorityPromotionGuard
  ≡ NSClay.navierStokesPromotionGuard
physicsAuthorityGuardMatchesAdapter = refl

physicsTerminalPromotionImpossible :
  NSClay.NSClayDistanceFinalPromotion → ⊥
physicsTerminalPromotionImpossible =
  Physics.navierStokesTerminalPromotionImpossible

releasedCHeadStable :
  NSClay.releasedCHeadStatementStable ≡ true
releasedCHeadStable =
  NSClay.releasedCHeadStatementStableIsTrue

releasedDHeadStable :
  NSClay.releasedDHeadStatementStable ≡ true
releasedDHeadStable =
  NSClay.releasedDHeadStatementStableIsTrue

releasedHeadCoordinateAuditNeedNotReopen :
  NSClay.releasedHeadRequiresReopeningCoordinateAudit ≡ false
releasedHeadCoordinateAuditNeedNotReopen =
  NSClay.releasedHeadDoesNotRequireReopeningCoordinateAudit


------------------------------------------------------------------------
-- R829-vector instantaneous snapshot agreement and non-promotion.
------------------------------------------------------------------------

adapterInstantaneousVectorSnapshotClosed :
  NSClay.instantaneousVectorSnapshotClosed ≡ true
adapterInstantaneousVectorSnapshotClosed =
  NSClay.instantaneousVectorSnapshotClosedIsTrue

adapterInstantaneousRepositoryRateNegative :
  NSClay.instantaneousRepositoryRateStrictlyNegative ≡ true
adapterInstantaneousRepositoryRateNegative =
  NSClay.instantaneousRepositoryRateStrictlyNegativeIsTrue

adapterRealFiniteODETransportStillOpen :
  NSClay.realFiniteODETransportClosed ≡ false
adapterRealFiniteODETransportStillOpen =
  NSClay.realFiniteODETransportStillOpen

adapterUniversalR823ReserveStillUnrefuted :
  NSClay.universalR823IntegratedReserveRefuted ≡ false
adapterUniversalR823ReserveStillUnrefuted =
  NSClay.universalR823IntegratedReserveStillUnrefuted

adapterInstantaneousSnapshotClayStillFalse :
  NSClay.instantaneousSnapshotClayPromotion ≡ false
adapterInstantaneousSnapshotClayStillFalse =
  NSClay.instantaneousSnapshotClayPromotionStillFalse

toeInstantaneousVectorSnapshotMatchesAdapter :
  TOE.toeNavierStokesInstantaneousVectorSnapshotClosed
  ≡ NSClay.instantaneousVectorSnapshotClosed
toeInstantaneousVectorSnapshotMatchesAdapter = refl

toeInstantaneousSnapshotClayMatchesAdapter :
  TOE.toeNavierStokesInstantaneousSnapshotClayPromotion
  ≡ NSClay.instantaneousSnapshotClayPromotion
toeInstantaneousSnapshotClayMatchesAdapter = refl

unifierInstantaneousVectorSnapshotMatchesAdapter :
  U.unifierNavierStokesInstantaneousVectorSnapshotClosed
  ≡ NSClay.instantaneousVectorSnapshotClosed
unifierInstantaneousVectorSnapshotMatchesAdapter = refl

unifierUniversalR823ReserveMatchesAdapter :
  U.unifierNavierStokesUniversalR823IntegratedReserveRefuted
  ≡ NSClay.universalR823IntegratedReserveRefuted
unifierUniversalR823ReserveMatchesAdapter = refl

physicsInstantaneousVectorSnapshotMatchesAdapter :
  Physics.navierStokesInstantaneousVectorSnapshotClosed
  ≡ NSClay.instantaneousVectorSnapshotClosed
physicsInstantaneousVectorSnapshotMatchesAdapter = refl

physicsRealFiniteODETransportMatchesAdapter :
  Physics.navierStokesRealFiniteODETransportClosed
  ≡ NSClay.realFiniteODETransportClosed
physicsRealFiniteODETransportMatchesAdapter = refl


------------------------------------------------------------------------
-- R736 current periodic-B shared weighted wall.
------------------------------------------------------------------------

adapterSharedWeightedExactlyTwoLeaves :
  NSClay.currentSharedWeightedExactlyTwoLeaves ≡ true
adapterSharedWeightedExactlyTwoLeaves =
  NSClay.currentSharedWeightedExactlyTwoLeavesIsTrue

adapterSharedWeightedSameCarrier :
  NSClay.currentSharedWeightedSameCarrier ≡ true
adapterSharedWeightedSameCarrier =
  NSClay.currentSharedWeightedSameCarrierIsTrue

adapterSharedWeightedCarrierIsInputLaplacian :
  NSClay.currentSharedWeightedCarrierIsInputLaplacian ≡ true
adapterSharedWeightedCarrierIsInputLaplacian =
  NSClay.currentSharedWeightedCarrierIsInputLaplacianIsTrue

adapterWeightedPlusEndpointStillOpen :
  NSClay.currentWeightedPlusEndpointClosed ≡ false
adapterWeightedPlusEndpointStillOpen =
  NSClay.currentWeightedPlusEndpointStillOpen

adapterAugmentedCriticalWeightedStillOpen :
  NSClay.currentAugmentedCriticalWeightedClosed ≡ false
adapterAugmentedCriticalWeightedStillOpen =
  NSClay.currentAugmentedCriticalWeightedStillOpen

adapterSharedWeightedLeavesBuildBarrier :
  NSClay.currentSharedWeightedLeavesBuildBarrier ≡ true
adapterSharedWeightedLeavesBuildBarrier =
  NSClay.currentSharedWeightedLeavesBuildBarrierIsTrue

adapterR726NotIndependent :
  NSClay.legacyR726IndependentLeafRequired ≡ false
adapterR726NotIndependent =
  NSClay.legacyR726IndependentLeafNotRequired

adapterStrictMarginR406NotIndependent :
  NSClay.legacyStrictMarginR406IndependentLeafRequired ≡ false
adapterStrictMarginR406NotIndependent =
  NSClay.legacyStrictMarginR406IndependentLeafNotRequired

adapterQPlusMinusShortcutStillCircular :
  NSClay.barrierDependentQPlusMinusShortcutAdmissible ≡ false
adapterQPlusMinusShortcutStillCircular =
  NSClay.barrierDependentQPlusMinusShortcutStillCircular

adapterSharedWeightedClayStillFalse :
  NSClay.currentSharedWeightedClayPromotion ≡ false
adapterSharedWeightedClayStillFalse =
  NSClay.currentSharedWeightedClayPromotionStillFalse


------------------------------------------------------------------------
-- Consumer agreement for the current R736 wall.
------------------------------------------------------------------------

toeSharedWeightedLeafCountMatchesAdapter :
  TOE.toeNavierStokesSharedWeightedExactlyTwoLeaves
  ≡ NSClay.currentSharedWeightedExactlyTwoLeaves
toeSharedWeightedLeafCountMatchesAdapter = refl

toeWeightedPlusEndpointMatchesAdapter :
  TOE.toeNavierStokesWeightedPlusEndpointClosed
  ≡ NSClay.currentWeightedPlusEndpointClosed
toeWeightedPlusEndpointMatchesAdapter = refl

toeAugmentedCriticalWeightedMatchesAdapter :
  TOE.toeNavierStokesAugmentedCriticalWeightedClosed
  ≡ NSClay.currentAugmentedCriticalWeightedClosed
toeAugmentedCriticalWeightedMatchesAdapter = refl

toeSharedWeightedClayMatchesAdapter :
  TOE.toeNavierStokesSharedWeightedClayPromotion
  ≡ NSClay.currentSharedWeightedClayPromotion
toeSharedWeightedClayMatchesAdapter = refl

toeSharedWeightedClayStillFalse :
  TOE.toeNavierStokesSharedWeightedClayPromotion ≡ false
toeSharedWeightedClayStillFalse =
  TOE.toeNavierStokesSharedWeightedClayPromotionStillFalse

unifierSharedWeightedLeafCountMatchesAdapter :
  U.unifierNavierStokesSharedWeightedExactlyTwoLeaves
  ≡ NSClay.currentSharedWeightedExactlyTwoLeaves
unifierSharedWeightedLeafCountMatchesAdapter = refl

unifierWeightedPlusEndpointMatchesAdapter :
  U.unifierNavierStokesWeightedPlusEndpointClosed
  ≡ NSClay.currentWeightedPlusEndpointClosed
unifierWeightedPlusEndpointMatchesAdapter = refl

unifierAugmentedCriticalWeightedMatchesAdapter :
  U.unifierNavierStokesAugmentedCriticalWeightedClosed
  ≡ NSClay.currentAugmentedCriticalWeightedClosed
unifierAugmentedCriticalWeightedMatchesAdapter = refl

unifierSharedWeightedClayMatchesAdapter :
  U.unifierNavierStokesSharedWeightedClayPromotion
  ≡ NSClay.currentSharedWeightedClayPromotion
unifierSharedWeightedClayMatchesAdapter = refl

unifierSharedWeightedClayStillFalse :
  U.unifierNavierStokesSharedWeightedClayPromotion ≡ false
unifierSharedWeightedClayStillFalse =
  U.unifierNavierStokesSharedWeightedClayPromotionStillFalse

physicsSharedWeightedLeafCountMatchesAdapter :
  Physics.navierStokesSharedWeightedExactlyTwoLeaves
  ≡ NSClay.currentSharedWeightedExactlyTwoLeaves
physicsSharedWeightedLeafCountMatchesAdapter = refl

physicsWeightedPlusEndpointMatchesAdapter :
  Physics.navierStokesWeightedPlusEndpointClosed
  ≡ NSClay.currentWeightedPlusEndpointClosed
physicsWeightedPlusEndpointMatchesAdapter = refl

physicsAugmentedCriticalWeightedMatchesAdapter :
  Physics.navierStokesAugmentedCriticalWeightedClosed
  ≡ NSClay.currentAugmentedCriticalWeightedClosed
physicsAugmentedCriticalWeightedMatchesAdapter = refl

physicsSharedWeightedClayMatchesAdapter :
  Physics.navierStokesSharedWeightedClayPromotion
  ≡ NSClay.currentSharedWeightedClayPromotion
physicsSharedWeightedClayMatchesAdapter = refl

physicsSharedWeightedClayStillFalse :
  Physics.navierStokesSharedWeightedClayPromotion ≡ false
physicsSharedWeightedClayStillFalse =
  Physics.navierStokesSharedWeightedClayPromotionStillFalse

roadmapContinuumBKMStillOpen :
  NSClay.continuumBKMPassageConstructed ≡ false
roadmapContinuumBKMStillOpen =
  NSClay.continuumBKMPassageStillOpen

roadmapAllDataBridgeStillOpen :
  NSClay.allDataBridgeConstructed ≡ false
roadmapAllDataBridgeStillOpen =
  NSClay.allDataBridgeStillOpen

roadmapSubmissionPacketStillNotReady :
  NSClay.submissionPacketReady ≡ false
roadmapSubmissionPacketStillNotReady =
  NSClay.submissionPacketStillNotReady

roadmapClayEligibilityStillFalse :
  NSClay.clayEligible ≡ false
roadmapClayEligibilityStillFalse =
  NSClay.clayEligibilityStillFalse

toeRoadmapClayEligibilityMatchesAdapter :
  TOE.toeNavierStokesClayEligible ≡ NSClay.clayEligible
toeRoadmapClayEligibilityMatchesAdapter = refl

unifierRoadmapClayEligibilityMatchesAdapter :
  U.unifierNavierStokesClayEligible ≡ NSClay.clayEligible
unifierRoadmapClayEligibilityMatchesAdapter = refl

physicsRoadmapClayEligibilityMatchesAdapter :
  Physics.navierStokesClayEligible ≡ NSClay.clayEligible
physicsRoadmapClayEligibilityMatchesAdapter = refl

toeRoadmapContinuumBKMMatchesAdapter :
  TOE.toeNavierStokesContinuumBKMPassageConstructed
  ≡ NSClay.continuumBKMPassageConstructed
toeRoadmapContinuumBKMMatchesAdapter = refl

unifierRoadmapAllDataMatchesAdapter :
  U.unifierNavierStokesAllDataBridgeConstructed
  ≡ NSClay.allDataBridgeConstructed
unifierRoadmapAllDataMatchesAdapter = refl

physicsRoadmapSubmissionMatchesAdapter :
  Physics.navierStokesSubmissionPacketReady
  ≡ NSClay.submissionPacketReady
physicsRoadmapSubmissionMatchesAdapter = refl
