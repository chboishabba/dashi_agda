module DASHI.Physics.Plasma.MHDInductionResidualConsumerBidiExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Plasma.MHDHelicalElsasserTriadHypervoxelExact as V
import DASHI.Physics.Plasma.MHDHelicalElsasserInteractionAdmissibilityExact as A

------------------------------------------------------------------------
-- INDUCTION-SECTOR RESIDUAL CONSUMER
--
-- Momentum cancellation does not close the induction equation.  This owner
-- keeps the induction channel open as an explicit residual obligation.
------------------------------------------------------------------------

record InductionResidualReceipt
    (voxel : V.MHDHelicalElsasserTriadHypervoxel) : Set₁ where
  constructor induction-residual-receipt
  field
    sectorIsInduction : V.equationSector voxel ≡ V.inductionSector
    admittedInteraction : A.AdmittedMHDTriadInteraction voxel
    outputSignedRadiusFactor : Set
    mixedAmplitudeChannel : Set
    literalInductionCoefficient : Set
    residualBudget : Set
    sameObjectResidualReceipt : Set

open InductionResidualReceipt public

record InductionResidualBoundary : Set where
  constructor induction-residual-boundary
  field
    momentumCommutatorClosesInductionSector : Bool
    momentumCommutatorClosesInductionSectorIsFalse :
      momentumCommutatorClosesInductionSector ≡ false

    inductionCoefficientAutomaticallyHasThreeSlotZeroSum : Bool
    inductionCoefficientAutomaticallyHasThreeSlotZeroSumIsFalse :
      inductionCoefficientAutomaticallyHasThreeSlotZeroSum ≡ false

    inductionResidualRequiresIndependentReceipt : Bool
    inductionResidualRequiresIndependentReceiptIsTrue :
      inductionResidualRequiresIndependentReceipt ≡ true

canonicalInductionResidualBoundary : InductionResidualBoundary
canonicalInductionResidualBoundary =
  induction-residual-boundary false refl false refl true refl
