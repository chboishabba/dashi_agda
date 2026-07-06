module DASHI.Physics.Closure.NSTriadKNSchurResidueScale where

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem as OperatorCN
import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix as CrossMatrix
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)

------------------------------------------------------------------------
-- Schur residue-scale bridge surface.
--
-- This is the theorem layer between a q_gap(N) >= c / N^2 statement and the
-- PDE-facing residue control used later in the BKM lane.

record NSTriadKNSchurResidueScaleModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    qGapModel :
      QGap.NSTriadKNQGapTransferModel {ℓS} {ℓE} {ℓV} {ℓR}

    schurResidueFunctional :
      Shell (QGap.qGapDecompositionModel qGapModel) ->
      CrossMatrix.Bound
        (WeightedSchur.profileMatrixModel
          (OperatorCN.weightedSchurModel
            (QGap.operatorCNModel qGapModel)))

    schurResidueTarget :
      Shell (QGap.qGapDecompositionModel qGapModel) ->
      CrossMatrix.Bound
        (WeightedSchur.profileMatrixModel
          (OperatorCN.weightedSchurModel
            (QGap.operatorCNModel qGapModel)))

    qGapN2ControlsSchurResidue :
      (N : Shell (QGap.qGapDecompositionModel qGapModel)) ->
      CrossMatrix._≤_
        (WeightedSchur.profileMatrixModel
          (OperatorCN.weightedSchurModel
            (QGap.operatorCNModel qGapModel)))
        (schurResidueFunctional N)
        (schurResidueTarget N)

open NSTriadKNSchurResidueScaleModel public

------------------------------------------------------------------------
-- Proof-derived gate definitions.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

schurResidueScaleClosed :
  QGap.ResidueScaleCompatibility → Bool
schurResidueScaleClosed compat with QGap.qGapTransferClosed compat
... | true = true
... | false = false

schurResidueScaleClosedIsTrue :
  (compat : QGap.ResidueScaleCompatibility) →
  QGap.compatibilityRouteClosed compat ≡ true →
  schurResidueScaleClosed compat ≡ true
schurResidueScaleClosedIsTrue compat routeClosed
  rewrite QGap.qGapTransferClosedIsTrue compat routeClosed = refl
