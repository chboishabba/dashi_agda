{-# OPTIONS --safe #-}
module DASHI.Unified.FleetFormalGapTargetTOEValidation where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier

-- Exact same-owner agreement. R4/R5 fleet quantities remain external
-- planning receipts and do not become formal theorem discharge.

toeFleetReceiptMatchesOwner :
  TOE.toeFleetFormalGapTargetReceipt
  ≡ Fleet.canonicalFleetFormalGapTargetReceipt
toeFleetReceiptMatchesOwner = refl

unifierFleetReceiptMatchesOwner :
  Unifier.unifierFleetFormalGapTargetReceipt
  ≡ Fleet.canonicalFleetFormalGapTargetReceipt
unifierFleetReceiptMatchesOwner = refl

toeFleetZKPFrameMatchesOwner :
  TOE.toeFleetFormalGapZKPFrame
  ≡ Fleet.canonicalFleetFormalGapZKPFrame
toeFleetZKPFrameMatchesOwner = refl

unifierFleetZKPFrameMatchesOwner :
  Unifier.unifierFleetFormalGapZKPFrame
  ≡ Fleet.canonicalFleetFormalGapZKPFrame
unifierFleetZKPFrameMatchesOwner = refl

toeEigenPriorityStillNotProof :
  Fleet.FleetEigenPriorityCreatesProof → ⊥
toeEigenPriorityStillNotProof =
  TOE.toeFleetEigenPriorityDoesNotCreateProof

unifierEigenPriorityStillNotProof :
  Fleet.FleetEigenPriorityCreatesProof → ⊥
unifierEigenPriorityStillNotProof =
  Unifier.unifierFleetEigenPriorityDoesNotCreateProof

toeExternalCountStillNotDischarge :
  Fleet.FleetExternalCountCreatesFormalDischarge → ⊥
toeExternalCountStillNotDischarge =
  TOE.toeFleetExternalCountDoesNotCreateFormalDischarge

unifierExternalCountStillNotDischarge :
  Fleet.FleetExternalCountCreatesFormalDischarge → ⊥
unifierExternalCountStillNotDischarge =
  Unifier.unifierFleetExternalCountDoesNotCreateFormalDischarge

toeDischargedFibresRemainExcluded :
  Fleet.FleetDischargedFibreRetargetPermission → ⊥
toeDischargedFibresRemainExcluded =
  TOE.toeFleetDischargedFibresRemainOutOfTarget

unifierDischargedFibresRemainExcluded :
  Fleet.FleetDischargedFibreRetargetPermission → ⊥
unifierDischargedFibresRemainExcluded =
  Unifier.unifierFleetDischargedFibresRemainOutOfTarget

toeContradictionGapsRemainSeparate :
  Fleet.FleetContradictionGapReclassificationPermission → ⊥
toeContradictionGapsRemainSeparate =
  TOE.toeFleetContradictionGapsRemainSeparate

unifierContradictionGapsRemainSeparate :
  Fleet.FleetContradictionGapReclassificationPermission → ⊥
unifierContradictionGapsRemainSeparate =
  Unifier.unifierFleetContradictionGapsRemainSeparate
