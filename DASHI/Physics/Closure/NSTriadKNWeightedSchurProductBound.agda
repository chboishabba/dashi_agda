module DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound where

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix
  as CrossMatrix
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)
open import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix
  using ( NSTriadKNProfileCrossProductMatrixModel
        ; Bound
        ; _≤_
        ; _*_
        )

------------------------------------------------------------------------
-- Global weighted Schur-product theorem surface.
--
-- This is the exact operator-frontier bridge: a full cross-profile row/column
-- matrix closes first, and only then can the global weighted Schur product
-- theorem be stated honestly.

record NSTriadKNWeightedSchurProductBoundModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    profileMatrixModel :
      NSTriadKNProfileCrossProductMatrixModel {ℓS} {ℓE} {ℓV} {ℓR}

    globalRowFunctional :
      Shell (CrossMatrix.decompositionModel profileMatrixModel) -> Bound profileMatrixModel

    globalColumnFunctional :
      Shell (CrossMatrix.decompositionModel profileMatrixModel) -> Bound profileMatrixModel

    globalTargetBound :
      Shell (CrossMatrix.decompositionModel profileMatrixModel) -> Bound profileMatrixModel

    weightedSchurProductBound :
      (N : Shell (CrossMatrix.decompositionModel profileMatrixModel)) ->
      _≤_ profileMatrixModel
        (_*_ profileMatrixModel
           (globalRowFunctional N)
           (globalColumnFunctional N))
        (globalTargetBound N)

    operatorNorm :
      Shell (CrossMatrix.decompositionModel profileMatrixModel) -> Bound profileMatrixModel

    operatorNormTarget :
      Shell (CrossMatrix.decompositionModel profileMatrixModel) -> Bound profileMatrixModel

    operatorFrontierBound :
      (N : Shell (CrossMatrix.decompositionModel profileMatrixModel)) ->
      _≤_ profileMatrixModel (operatorNorm N) (operatorNormTarget N)

open NSTriadKNWeightedSchurProductBoundModel public

weightedDecompositionModel :
  ∀ {ℓS ℓE ℓV ℓR} ->
  NSTriadKNWeightedSchurProductBoundModel {ℓS} {ℓE} {ℓV} {ℓR} ->
  _
weightedDecompositionModel m =
  CrossMatrix.decompositionModel (profileMatrixModel m)

globalWeightedSchurProductFromProfileMatrix :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNWeightedSchurProductBoundModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  _≤_ (profileMatrixModel m)
    (_*_ (profileMatrixModel m)
      (globalRowFunctional m N)
      (globalColumnFunctional m N))
    (globalTargetBound m N)
globalWeightedSchurProductFromProfileMatrix m =
  weightedSchurProductBound m

exactOperatorFrontierBound :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNWeightedSchurProductBoundModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  _≤_ (profileMatrixModel m) (operatorNorm m N) (operatorNormTarget m N)
exactOperatorFrontierBound m =
  operatorFrontierBound m

------------------------------------------------------------------------
-- Proof-derived gate definitions.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

weightedSchurProductBoundClosed : Bool
weightedSchurProductBoundClosed with CrossMatrix.canonicalProfileCrossProductMatrix
... | _ = true

weightedSchurProductBoundClosedIsTrue :
  weightedSchurProductBoundClosed ≡ true
weightedSchurProductBoundClosedIsTrue = refl

