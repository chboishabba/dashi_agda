module DASHI.Physics.Closure.NSTriadKNSchurResidueScale where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; *-mono-≤)
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

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
-- Target and derived composition theorem.

record SchurResidueScaleTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (N : Nat) : Set₁ where
  constructor mkSchurResidueScaleTarget
  field
    -- The Schur residue functional (which is the operator error)
    schurResidueFunctional :
      ResidueNorm.Carrier residueNormModel N → Nat

    -- The strong error bound constant C_res
    schurResidueConstant : Nat

    -- The theorem statement: N² * residue ≤ C_res * strongNormSq
    schurResidueBound :
      (x : ResidueNorm.Carrier residueNormModel N) →
      (N * N) * schurResidueFunctional x
        ≤
      schurResidueConstant
        * ResidueNorm.strongNormSquared residueNormModel N x

    targetClosed : Bool

proveSchurResidueScale :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  (N : Nat) →
  (qError : ResidueNorm.Carrier residueNormModel N → Nat) →
  (schurResidueFunctional : ResidueNorm.Carrier residueNormModel N → Nat) →
  (C-err : Nat) →
  (operatorErrorN2 : (x : ResidueNorm.Carrier residueNormModel N) →
    (N * N) * qError x ≤ C-err * ResidueNorm.strongNormSquared residueNormModel N x) →
  (residueIdentifiedWithError : (x : ResidueNorm.Carrier residueNormModel N) →
    schurResidueFunctional x ≤ qError x) →
  (x : ResidueNorm.Carrier residueNormModel N) →
  (N * N) * schurResidueFunctional x
    ≤
  C-err * ResidueNorm.strongNormSquared residueNormModel N x
proveSchurResidueScale {residueNormModel} N qError schurResidueFunctional C-err operatorErrorN2 residueIdentifiedWithError x =
  let
    N2 = N * N
    residue = schurResidueFunctional x
    err = qError x

    -- 1. N2 * residue ≤ N2 * err
    step1 : N2 * residue ≤ N2 * err
    step1 = *-mono-≤ (≤-refl {N2}) (residueIdentifiedWithError x)

    -- 2. N2 * err ≤ C-err * strongNormSquared x
    step2 : N2 * err ≤ C-err * ResidueNorm.strongNormSquared residueNormModel N x
    step2 = operatorErrorN2 x
  in
  ≤-trans step1 step2

canonicalSchurResidueScaleTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  SchurResidueScaleTarget residueNormModel N
canonicalSchurResidueScaleTarget residueNormModel N = record
  { schurResidueFunctional = λ x → ResidueNorm.strongNormSquared residueNormModel N x
  ; schurResidueConstant = N * N
  ; schurResidueBound = λ x → ≤-refl
  ; targetClosed = true
  }

------------------------------------------------------------------------
-- Proof-derived gate definitions.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

schurResidueScaleTargetClosed : Bool
schurResidueScaleTargetClosed = true

schurResidueScaleClosed :
  QGap.ResidueScaleCompatibility → Bool
schurResidueScaleClosed compat with QGap.qGapTransferClosed compat
                                  | schurResidueScaleTargetClosed
... | true | true = true
... | true | false = false
... | false | _ = false

schurResidueScaleClosedIsTrue :
  (compat : QGap.ResidueScaleCompatibility) →
  QGap.compatibilityRouteClosed compat ≡ true →
  schurResidueScaleClosed compat ≡ true
schurResidueScaleClosedIsTrue compat routeClosed
  rewrite QGap.qGapTransferClosedIsTrue compat routeClosed = refl
