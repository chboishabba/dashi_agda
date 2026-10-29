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


------------------------------------------------------------------------
-- Canonical current four-lane problem receipt validation.
------------------------------------------------------------------------

adapterCurrentProblemBM2FiniteFoldClosed :
  NSClay.laneBM2FiniteFoldClosed
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ true
adapterCurrentProblemBM2FiniteFoldClosed =
  NSClay.currentProblemBM2FiniteFoldClosed

adapterCurrentProblemBM2SamplewisePaymentStillAnalytic :
  NSClay.laneBM2SamplewisePhysicalPaymentStillAnalytic
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ true
adapterCurrentProblemBM2SamplewisePaymentStillAnalytic =
  NSClay.currentProblemBM2SamplewisePaymentRemainsAnalytic

adapterCurrentProblemBM2GalerkinFoldStillAnalytic :
  NSClay.laneBM2LiteralDissipationFoldStillAnalytic
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ true
adapterCurrentProblemBM2GalerkinFoldStillAnalytic =
  NSClay.currentProblemBM2GalerkinFoldRemainsAnalytic

adapterCurrentProblemBWeightedPlusStillOpen :
  NSClay.laneBWeightedPlusEndpointClosed
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ false
adapterCurrentProblemBWeightedPlusStillOpen =
  NSClay.currentProblemBWeightedPlusEndpointStillOpen

adapterCurrentProblemBAugmentedStillOpen :
  NSClay.laneBAugmentedCriticalWeightedClosed
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ false
adapterCurrentProblemBAugmentedStillOpen =
  NSClay.currentProblemBAugmentedCriticalWeightedStillOpen

adapterCurrentProblemCDKernelBuildStillExternal :
  NSClay.laneCDIndependentKernelBuildWitnessedHere
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ false
adapterCurrentProblemCDKernelBuildStillExternal =
  NSClay.currentProblemCDKernelBuildStillExternal

adapterCurrentProblemCDReconstructionDoesNotGateAudit :
  NSClay.laneCDIndependentReconstructionGatesAudit
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ false
adapterCurrentProblemCDReconstructionDoesNotGateAudit =
  NSClay.currentProblemCDReconstructionDoesNotGateAudit

toeCurrentProblemBM2FiniteFoldMatchesAdapter :
  TOE.toeNavierStokesCurrentProblemBM2FiniteFoldClosed
  ≡ NSClay.currentProblemBM2FiniteFoldClosed
toeCurrentProblemBM2FiniteFoldMatchesAdapter = refl

toeCurrentProblemWeightedPlusMatchesAdapter :
  TOE.toeNavierStokesCurrentProblemBWeightedPlusStillOpen
  ≡ NSClay.currentProblemBWeightedPlusEndpointStillOpen
toeCurrentProblemWeightedPlusMatchesAdapter = refl

toeCurrentProblemAugmentedMatchesAdapter :
  TOE.toeNavierStokesCurrentProblemBAugmentedStillOpen
  ≡ NSClay.currentProblemBAugmentedCriticalWeightedStillOpen
toeCurrentProblemAugmentedMatchesAdapter = refl

unifierCurrentProblemBM2FiniteFoldMatchesAdapter :
  U.unifierNavierStokesCurrentProblemBM2FiniteFoldClosed
  ≡ NSClay.currentProblemBM2FiniteFoldClosed
unifierCurrentProblemBM2FiniteFoldMatchesAdapter = refl

unifierCurrentProblemWeightedPlusMatchesAdapter :
  U.unifierNavierStokesCurrentProblemBWeightedPlusStillOpen
  ≡ NSClay.currentProblemBWeightedPlusEndpointStillOpen
unifierCurrentProblemWeightedPlusMatchesAdapter = refl

physicsCurrentProblemBM2FiniteFoldMatchesAdapter :
  Physics.navierStokesCurrentProblemBM2FiniteFoldClosed
  ≡ NSClay.currentProblemBM2FiniteFoldClosed
physicsCurrentProblemBM2FiniteFoldMatchesAdapter = refl

physicsCurrentProblemWeightedPlusMatchesAdapter :
  Physics.navierStokesCurrentProblemBWeightedPlusStillOpen
  ≡ NSClay.currentProblemBWeightedPlusEndpointStillOpen
physicsCurrentProblemWeightedPlusMatchesAdapter = refl


adapterCurrentProblemBR829VectorClosed :
  NSClay.laneBR829VectorClosed
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ true
adapterCurrentProblemBR829VectorClosed =
  NSClay.currentProblemBR829VectorClosed

adapterCurrentProblemBR829InstantaneousRateStrictlyNegative :
  NSClay.laneBR829InstantaneousRateStrictlyNegative
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ true
adapterCurrentProblemBR829InstantaneousRateStrictlyNegative =
  NSClay.currentProblemBR829InstantaneousRateStrictlyNegative

adapterCurrentProblemBR829RealODEStillOpen :
  NSClay.laneBR829RealFiniteODETransportClosed
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ false
adapterCurrentProblemBR829RealODEStillOpen =
  NSClay.currentProblemBR829RealFiniteODETransportStillOpen

adapterCurrentProblemBR823IntegratedReserveStillNotRefuted :
  NSClay.laneBR823IntegratedReserveRefuted
    NSClay.canonicalNavierStokesCurrentProblemReceipt ≡ false
adapterCurrentProblemBR823IntegratedReserveStillNotRefuted =
  NSClay.currentProblemBR823IntegratedReserveStillNotRefuted

toeCurrentProblemBR829VectorMatchesAdapter :
  TOE.toeNavierStokesCurrentProblemBR829VectorClosed
  ≡ NSClay.currentProblemBR829VectorClosed
toeCurrentProblemBR829VectorMatchesAdapter = refl

toeCurrentProblemBR829RealODEMatchesAdapter :
  TOE.toeNavierStokesCurrentProblemBR829RealODEStillOpen
  ≡ NSClay.currentProblemBR829RealFiniteODETransportStillOpen
toeCurrentProblemBR829RealODEMatchesAdapter = refl

unifierCurrentProblemBR829VectorMatchesAdapter :
  U.unifierNavierStokesCurrentProblemBR829VectorClosed
  ≡ NSClay.currentProblemBR829VectorClosed
unifierCurrentProblemBR829VectorMatchesAdapter = refl

physicsCurrentProblemBR829VectorMatchesAdapter :
  Physics.navierStokesCurrentProblemBR829VectorClosed
  ≡ NSClay.currentProblemBR829VectorClosed
physicsCurrentProblemBR829VectorMatchesAdapter = refl
