{-# OPTIONS --safe #-}
module DASHI.Unified.BalabanFleetDual58TOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.BalabanFleetDual58TOEExact as Owner
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Everything as Unified

------------------------------------------------------------------------
-- Same-owner validation only.
------------------------------------------------------------------------

rootReceiptMatchesOwner :
  TOE.toeBalabanFleetDual58Receipt
  ≡ Owner.canonicalBalabanFleetDual58TOEReceipt
rootReceiptMatchesOwner = refl

unifierReceiptMatchesOwner :
  Unifier.unifierBalabanFleetDual58Receipt
  ≡ Owner.canonicalBalabanFleetDual58TOEReceipt
unifierReceiptMatchesOwner = refl

unifiedReceiptMatchesOwner :
  Unified.unifiedBalabanFleetDual58Receipt
  ≡ Owner.canonicalBalabanFleetDual58TOEReceipt
unifiedReceiptMatchesOwner = refl

fleet58RemainsFleet58 :
  Owner.fleetFormalGapCount Owner.canonicalBalabanFleetDual58TOEReceipt ≡ 58
fleet58RemainsFleet58 =
  Owner.fleet58RemainsFleet58

gate458RemainsGate458 :
  Owner.gate4GapCount Owner.canonicalBalabanFleetDual58TOEReceipt ≡ 58
gate458RemainsGate458 =
  Owner.gate458RemainsGate458

fleet584RemainsDischarged :
  Owner.fleetDischargedFibres Owner.canonicalBalabanFleetDual58TOEReceipt ≡ 584
fleet584RemainsDischarged =
  Owner.fleet584RemainsDischarged

fleet44RemainsContradiction :
  Owner.fleetContradictionGaps Owner.canonicalBalabanFleetDual58TOEReceipt ≡ 44
fleet44RemainsContradiction =
  Owner.fleet44RemainsContradiction

equal58DoesNotIdentifyObjects :
  Owner.Equal58CardinalityCreatesSameObject → ⊥
equal58DoesNotIdentifyObjects =
  Owner.equal58CardinalityDoesNotCreateSameObject

fleetEigenPriorityStillNotProof :
  Fleet.FleetEigenPriorityCreatesProof → ⊥
fleetEigenPriorityStillNotProof =
  Fleet.fleetEigenPriorityDoesNotCreateProof

fleetExternalCountStillNotFormalDischarge :
  Fleet.FleetExternalCountCreatesFormalDischarge → ⊥
fleetExternalCountStillNotFormalDischarge =
  Fleet.fleetExternalCountDoesNotCreateFormalDischarge

fleetDischargedFibresStillProtected :
  Fleet.FleetDischargedFibreRetargetPermission → ⊥
fleetDischargedFibresStillProtected =
  Fleet.fleetDischargedFibresCannotBeRetargetedByThisBoundary

fleetContradictionsStaySeparate :
  Fleet.FleetContradictionGapReclassificationPermission → ⊥
fleetContradictionsStaySeparate =
  Fleet.fleetContradictionsCannotBeRelabelledAsFormalGaps
