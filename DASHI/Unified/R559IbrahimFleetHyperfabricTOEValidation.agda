{-# OPTIONS --safe #-}
module DASHI.Unified.R559IbrahimFleetHyperfabricTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)
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

fleetEigenPriorityStillDoesNotCreateProof :
  Fleet.eigenvalueMagnitudeCreatesProofAuthority
    Owner.fleetFormalGapTargetReceipt ≡ false
fleetEigenPriorityStillDoesNotCreateProof =
  Owner.fleetEigenPriorityDoesNotCreateProof

fleetCountStillDoesNotCreateFormalDischarge :
  Fleet.externalCountCreatesFormalProof
    Owner.fleetFormalGapTargetReceipt ≡ false
fleetCountStillDoesNotCreateFormalDischarge =
  Owner.fleetExternalCountDoesNotCreateFormalDischarge

fleetDischargedFibresStillCannotBeRetargeted :
  Fleet.dischargedFibresRemainDischarged
    Owner.fleetFormalGapTargetReceipt ≡ true
fleetDischargedFibresStillCannotBeRetargeted =
  Owner.fleetDischargedFibresStayOutOfTarget

fleetContradictionGapsStillStaySeparate :
  Fleet.contradictionGapsRemainSeparate
    Owner.fleetFormalGapTargetReceipt ≡ true
fleetContradictionGapsStillStaySeparate =
  Owner.fleetContradictionGapsStaySeparate

toeYMGate4CountIs58 :
  TOE.toeYMGate4FormalGapsAre58
  ≡ Owner.ymGate4FormalGapsAre58
toeYMGate4CountIs58 = refl

unifierYMGate4CountIs58 :
  Unifier.unifierYMGate4FormalGapsAre58
  ≡ Owner.ymGate4FormalGapsAre58
unifierYMGate4CountIs58 = refl

toeFleet58DoesNotIdentifyYMGate4 :
  Owner.Fleet58EqualsYMGate4SameObject → ⊥
toeFleet58DoesNotIdentifyYMGate4 =
  TOE.toeFleet58DoesNotIdentifyYMGate4

unifierFleet58DoesNotIdentifyYMGate4 :
  Owner.Fleet58EqualsYMGate4SameObject → ⊥
unifierFleet58DoesNotIdentifyYMGate4 =
  Unifier.unifierFleet58DoesNotIdentifyYMGate4

------------------------------------------------------------------------
-- Live frontier, target split, and typed continuum no-go validation.
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
