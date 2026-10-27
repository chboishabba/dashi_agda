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
  Fleet.eigenvalueMagnitudeCreatesProofAuthority
    Fleet.canonicalFleetFormalGapTargetReceipt ≡ false
toeEigenPriorityStillNotProof =
  TOE.toeFleetEigenPriorityDoesNotCreateProof

unifierEigenPriorityStillNotProof :
  Fleet.eigenvalueMagnitudeCreatesProofAuthority
    Fleet.canonicalFleetFormalGapTargetReceipt ≡ false
unifierEigenPriorityStillNotProof =
  Unifier.unifierFleetEigenPriorityDoesNotCreateProof

toeExternalCountStillNotDischarge :
  Fleet.externalCountCreatesFormalProof
    Fleet.canonicalFleetFormalGapTargetReceipt ≡ false
toeExternalCountStillNotDischarge =
  TOE.toeFleetExternalCountDoesNotCreateFormalDischarge

unifierExternalCountStillNotDischarge :
  Fleet.externalCountCreatesFormalProof
    Fleet.canonicalFleetFormalGapTargetReceipt ≡ false
unifierExternalCountStillNotDischarge =
  Unifier.unifierFleetExternalCountDoesNotCreateFormalDischarge

toeDischargedFibresRemainExcluded :
  Fleet.dischargedFibresRemainDischarged
    Fleet.canonicalFleetFormalGapTargetReceipt ≡ true
toeDischargedFibresRemainExcluded =
  TOE.toeFleetDischargedFibresRemainOutOfTarget

unifierDischargedFibresRemainExcluded :
  Fleet.dischargedFibresRemainDischarged
    Fleet.canonicalFleetFormalGapTargetReceipt ≡ true
unifierDischargedFibresRemainExcluded =
  Unifier.unifierFleetDischargedFibresRemainOutOfTarget

toeContradictionGapsRemainSeparate :
  Fleet.contradictionGapsRemainSeparate
    Fleet.canonicalFleetFormalGapTargetReceipt ≡ true
toeContradictionGapsRemainSeparate =
  TOE.toeFleetContradictionGapsRemainSeparate

unifierContradictionGapsRemainSeparate :
  Fleet.contradictionGapsRemainSeparate
    Fleet.canonicalFleetFormalGapTargetReceipt ≡ true
unifierContradictionGapsRemainSeparate =
  Unifier.unifierFleetContradictionGapsRemainSeparate

toeFleetPlanningBoundaryMatchesOwner :
  TOE.toeFleetPlanningBoundary ≡ Fleet.fleetPlanningBoundary
toeFleetPlanningBoundaryMatchesOwner = refl

unifierFleetPlanningBoundaryMatchesOwner :
  Unifier.unifierFleetPlanningBoundary ≡ Fleet.fleetPlanningBoundary
unifierFleetPlanningBoundaryMatchesOwner = refl

toeFleetVectorCoordinateStillNotTruth :
  TOE.toeFleetVectorCoordinateDoesNotCreateTruth
  ≡ Fleet.fleetVectorCoordinateDoesNotCreateTruth
toeFleetVectorCoordinateStillNotTruth = refl

unifierFleetVectorCoordinateStillNotTruth :
  Unifier.unifierFleetVectorCoordinateDoesNotCreateTruth
  ≡ Fleet.fleetVectorCoordinateDoesNotCreateTruth
unifierFleetVectorCoordinateStillNotTruth = refl
