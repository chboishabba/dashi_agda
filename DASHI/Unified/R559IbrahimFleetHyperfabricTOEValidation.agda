{-# OPTIONS --safe #-}
module DASHI.Unified.R559IbrahimFleetHyperfabricTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import Data.Empty using (⊥)

import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Everything as Unified
import DASHI.Unified.R559IbrahimFleetHyperfabricTOEExact as Owner
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet
import DASHI.Physics.YangMills.CompactLieProofLevel as Proof

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


ymGate4FormalGapCountIs58 :
  Owner.ymGate4FormalGaps ≡ 58
ymGate4FormalGapCountIs58 =
  Owner.ymGate4FormalGapsAre58

ymGate4PaidReductionIsMachineChecked :
  Proof.promotable Owner.ymGate4PaidReductionLevel ≡ true
ymGate4PaidReductionIsMachineChecked =
  Proof.machineCheckedPromotes

ymGate4InhabitantsRemainNonPromoting :
  Proof.promotable Owner.ymGate4InhabitantsLevel ≡ false
ymGate4InhabitantsRemainNonPromoting =
  Proof.conditionalDoesNotSelfPromote

sameCardinalityDoesNotIdentifyFleetAndGate4 :
  Owner.Fleet58EqualsYMGate4SameObject → ⊥
sameCardinalityDoesNotIdentifyFleetAndGate4 =
  Owner.fleet58CardinalityDoesNotProveYMGate4Identity

