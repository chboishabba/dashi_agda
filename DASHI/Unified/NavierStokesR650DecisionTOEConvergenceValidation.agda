{-# OPTIONS --safe #-}
module DASHI.Unified.NavierStokesR650DecisionTOEConvergenceValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.NavierStokesR650DecisionTOEConvergenceExact as NS
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as U
import DASHI.Unified.Physics as Physics

adapterSnapshotClosed :
  NS.snapshotIdentificationClosed ≡ true
adapterSnapshotClosed =
  NS.snapshotIdentificationClosedIsTrue

adapterInstantaneousRateNegative :
  NS.instantaneousRepositoryRateNegative ≡ true
adapterInstantaneousRateNegative =
  NS.instantaneousRepositoryRateNegativeIsTrue

adapterFiniteRealEncodingClosed :
  NS.canonicalFiniteRealStateEncoded ≡ true
adapterFiniteRealEncodingClosed =
  NS.canonicalFiniteRealStateEncodedIsTrue

adapterDegreeTwoCoordinatesClosed :
  NS.finiteRealRHSCoordinatesDegreeAtMostTwo ≡ true
adapterDegreeTwoCoordinatesClosed =
  NS.finiteRealRHSCoordinatesDegreeAtMostTwoIsTrue

adapterSelectedRateNormalFormClosed :
  NS.selectedRateNormalFormClosed ≡ true
adapterSelectedRateNormalFormClosed =
  NS.selectedRateNormalFormClosedIsTrue

adapterRealTrajectoryWeldOpen :
  NS.realTrajectoryCarrierWeldClosed ≡ false
adapterRealTrajectoryWeldOpen =
  NS.realTrajectoryCarrierWeldClosedIsFalse

adapterIntegratedDecisionOpen :
  NS.integratedR823DecisionClosed ≡ false
adapterIntegratedDecisionOpen =
  NS.integratedR823DecisionClosedIsFalse

adapterClayPromotionFalse :
  NS.clayPromotion ≡ false
adapterClayPromotionFalse =
  NS.clayPromotionIsFalse

toeReceiptMatchesAdapter :
  TOE.toeNavierStokesR650DecisionReceipt
  ≡ NS.canonicalNavierStokesR650DecisionTOEReceipt
toeReceiptMatchesAdapter = refl

unifierReceiptMatchesAdapter :
  U.nsR650DecisionTOEReceipt
  ≡ NS.canonicalNavierStokesR650DecisionTOEReceipt
unifierReceiptMatchesAdapter = refl

physicsReceiptMatchesAdapter :
  Physics.navierStokesR650DecisionReceipt
  ≡ NS.canonicalNavierStokesR650DecisionTOEReceipt
physicsReceiptMatchesAdapter = refl

toeOpenSeamMatchesAdapter :
  TOE.toeNavierStokesR650IntegratedDecisionRemainsOpen
  ≡ NS.integratedR823DecisionClosedIsFalse
toeOpenSeamMatchesAdapter = refl

unifierOpenSeamMatchesAdapter :
  U.nsR650IntegratedDecisionRemainsOpen
  ≡ NS.integratedR823DecisionClosedIsFalse
unifierOpenSeamMatchesAdapter = refl

physicsOpenSeamMatchesAdapter :
  Physics.navierStokesR650IntegratedDecisionRemainsOpen
  ≡ NS.integratedR823DecisionClosedIsFalse
physicsOpenSeamMatchesAdapter = refl

toeClayBoundaryMatchesAdapter :
  TOE.toeNavierStokesR650DecisionClayPromotionRemainsFalse
  ≡ NS.clayPromotionIsFalse
toeClayBoundaryMatchesAdapter = refl

unifierClayBoundaryMatchesAdapter :
  U.nsR650DecisionClayPromotionRemainsFalse
  ≡ NS.clayPromotionIsFalse
unifierClayBoundaryMatchesAdapter = refl

physicsClayBoundaryMatchesAdapter :
  Physics.navierStokesR650DecisionClayPromotionRemainsFalse
  ≡ NS.clayPromotionIsFalse
physicsClayBoundaryMatchesAdapter = refl
