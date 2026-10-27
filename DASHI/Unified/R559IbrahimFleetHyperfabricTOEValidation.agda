{-# OPTIONS --safe #-}
module DASHI.Unified.R559IbrahimFleetHyperfabricTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Everything as Unified
import DASHI.Unified.R559IbrahimFleetHyperfabricTOEExact as Owner
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet

toeReceiptMatchesOwner :
  TOE.toeR559IbrahimFleetHyperfabricReceipt
  ≡ Owner.canonicalR559IbrahimFleetHyperfabricTOEReceipt
toeReceiptMatchesOwner = refl

unifierReceiptMatchesOwner :
  Unifier.unifierR559IbrahimFleetHyperfabricReceipt
  ≡ Owner.canonicalR559IbrahimFleetHyperfabricTOEReceipt
unifierReceiptMatchesOwner = refl

unifiedReceiptMatchesOwner :
  Unified.unifiedR559IbrahimFleetHyperfabricReceipt
  ≡ Owner.canonicalR559IbrahimFleetHyperfabricTOEReceipt
unifiedReceiptMatchesOwner = refl

toeFormalGapTargetIs58 :
  TOE.toeFleetFormalGapsAre58
  ≡ Owner.fleetFormalGapsAre58
toeFormalGapTargetIs58 = refl

unifierFormalGapTargetIs58 :
  Unifier.unifierFleetFormalGapsAre58
  ≡ Owner.fleetFormalGapsAre58
unifierFormalGapTargetIs58 = refl

toeDischargedFibresRemain584 :
  TOE.toeFleetDischargedFibresAre584
  ≡ Owner.fleetDischargedFibresAre584
toeDischargedFibresRemain584 = refl

unifierDischargedFibresRemain584 :
  Unifier.unifierFleetDischargedFibresAre584
  ≡ Owner.fleetDischargedFibresAre584
unifierDischargedFibresRemain584 = refl

toeContradictionGapsRemain44 :
  TOE.toeFleetContradictionGapsAre44
  ≡ Owner.fleetContradictionGapsAre44
toeContradictionGapsRemain44 = refl

unifierContradictionGapsRemain44 :
  Unifier.unifierFleetContradictionGapsAre44
  ≡ Owner.fleetContradictionGapsAre44
unifierContradictionGapsRemain44 = refl

toePadicLossStillExact :
  Owner.PadicPrefixRecovery → ⊥
toePadicLossStillExact =
  TOE.toePadicPrefixCannotRecoverDiscardedDigit

unifierPadicLossStillExact :
  Owner.PadicPrefixRecovery → ⊥
unifierPadicLossStillExact =
  Unifier.unifierPadicPrefixCannotRecoverDiscardedDigit

toeStreamLossStillExact :
  Owner.StreamThirdPrefixRecovery → ⊥
toeStreamLossStillExact =
  TOE.toeTwoDigitStreamCannotRecoverThird

unifierStreamLossStillExact :
  Owner.StreamThirdPrefixRecovery → ⊥
unifierStreamLossStillExact =
  Unifier.unifierTwoDigitStreamCannotRecoverThird

fleetCountStillDoesNotCreateFormalDischarge :
  Fleet.FleetExternalCountCreatesFormalDischarge → ⊥
fleetCountStillDoesNotCreateFormalDischarge =
  Owner.fleetExternalCountDoesNotCreateFormalDischarge

fleetDischargedFibresStillCannotBeRetargeted :
  Fleet.FleetDischargedFibreRetargetPermission → ⊥
fleetDischargedFibresStillCannotBeRetargeted =
  Owner.fleetDischargedFibresStayOutOfTarget


------------------------------------------------------------------------
-- Live frontier, target split, and canonical continuum no-go validation.
------------------------------------------------------------------------

toeCurrentGate4FrontierMatchesOwner :
  TOE.toeCurrentGate4FrontierLedgerLevel
  ≡ Owner.currentGate4FrontierLedgerLevel
toeCurrentGate4FrontierMatchesOwner = refl

unifierCurrentGate4FrontierMatchesOwner :
  Unifier.unifierCurrentGate4FrontierLedgerLevel
  ≡ Owner.currentGate4FrontierLedgerLevel
unifierCurrentGate4FrontierMatchesOwner = refl

unifiedCurrentGate4FrontierMatchesOwner :
  Unified.unifiedCurrentGate4FrontierLedgerLevel
  ≡ Owner.currentGate4FrontierLedgerLevel
unifiedCurrentGate4FrontierMatchesOwner = refl

toeFleetTargetSelectionMatchesOwner :
  TOE.toeFleetFormalGapTargetSelected
  ≡ Owner.fleetFormalGapTargetSelected
toeFleetTargetSelectionMatchesOwner = refl

unifierFleetTargetSelectionMatchesOwner :
  Unifier.unifierFleetFormalGapTargetSelected
  ≡ Owner.fleetFormalGapTargetSelected
unifierFleetTargetSelectionMatchesOwner = refl

unifiedFleetTargetSelectionMatchesOwner :
  Unified.unifiedFleetFormalGapTargetSelected
  ≡ Owner.fleetFormalGapTargetSelected
unifiedFleetTargetSelectionMatchesOwner = refl

rootBalabanContinuumNoGoReachable :
  Owner.BalabanContinuumPromotion → ⊥
rootBalabanContinuumNoGoReachable =
  TOE.toeBalabanContinuumLimitPromotionImpossible

unifierBalabanContinuumNoGoReachable :
  Owner.BalabanContinuumPromotion → ⊥
unifierBalabanContinuumNoGoReachable =
  Unifier.unifierBalabanContinuumLimitPromotionImpossible

unifiedBalabanContinuumNoGoReachable :
  Owner.BalabanContinuumPromotion → ⊥
unifiedBalabanContinuumNoGoReachable =
  Unified.unifiedBalabanContinuumLimitPromotionImpossible

rootDepthContinuumNoGoReachable :
  Owner.DepthContinuumPromotion → ⊥
rootDepthContinuumNoGoReachable =
  TOE.toeDepthContinuumLimitPromotionImpossible

unifierDepthContinuumNoGoReachable :
  Owner.DepthContinuumPromotion → ⊥
unifierDepthContinuumNoGoReachable =
  Unifier.unifierDepthContinuumLimitPromotionImpossible

unifiedDepthContinuumNoGoReachable :
  Owner.DepthContinuumPromotion → ⊥
unifiedDepthContinuumNoGoReachable =
  Unified.unifiedDepthContinuumLimitPromotionImpossible
