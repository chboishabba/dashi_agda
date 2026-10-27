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


------------------------------------------------------------------------
-- Reused fleet receipt owners remain exactly the canonical owners.
------------------------------------------------------------------------

toeFleetCoordinateRebuildabilityReceiptMatchesOwner :
  TOE.toeFleetCoordinateRebuildabilityReceipt
  ≡ Fleet.fleetCoordinateRebuildabilityReceipt
toeFleetCoordinateRebuildabilityReceiptMatchesOwner = refl

unifierFleetCoordinateRebuildabilityReceiptMatchesOwner :
  Unifier.unifierFleetCoordinateRebuildabilityReceipt
  ≡ Fleet.fleetCoordinateRebuildabilityReceipt
unifierFleetCoordinateRebuildabilityReceiptMatchesOwner = refl

toeFleetNumericABIReceiptMatchesOwner :
  TOE.toeFleetNumericABIReceipt
  ≡ Fleet.fleetNumericABIReceipt
toeFleetNumericABIReceiptMatchesOwner = refl

unifierFleetNumericABIReceiptMatchesOwner :
  Unifier.unifierFleetNumericABIReceipt
  ≡ Fleet.fleetNumericABIReceipt
unifierFleetNumericABIReceiptMatchesOwner = refl

toeFleetResidualInvariantReceiptMatchesOwner :
  TOE.toeFleetResidualInvariantReceipt
  ≡ Fleet.fleetResidualInvariantReceipt
toeFleetResidualInvariantReceiptMatchesOwner = refl

unifierFleetResidualInvariantReceiptMatchesOwner :
  Unifier.unifierFleetResidualInvariantReceipt
  ≡ Fleet.fleetResidualInvariantReceipt
unifierFleetResidualInvariantReceiptMatchesOwner = refl

toeFleetPromotionObligationIndexMatchesOwner :
  TOE.toeFleetPromotionObligationIndex
  ≡ Fleet.fleetPromotionObligationIndex
toeFleetPromotionObligationIndexMatchesOwner = refl

unifierFleetPromotionObligationIndexMatchesOwner :
  Unifier.unifierFleetPromotionObligationIndex
  ≡ Fleet.fleetPromotionObligationIndex
unifierFleetPromotionObligationIndexMatchesOwner = refl

toeFleetPlanningTextStillDoesNotCreateFormalResidual :
  TOE.toeFleetPlanningTextDoesNotCreateFormalResidual
  ≡ Fleet.fleetPlanningTextDoesNotCreateFormalResidual
toeFleetPlanningTextStillDoesNotCreateFormalResidual = refl

unifierFleetPlanningTextStillDoesNotCreateFormalResidual :
  Unifier.unifierFleetPlanningTextDoesNotCreateFormalResidual
  ≡ Fleet.fleetPlanningTextDoesNotCreateFormalResidual
unifierFleetPlanningTextStillDoesNotCreateFormalResidual = refl
