module DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_*_ to _*ℕ_)
open import Data.Nat using () renaming (_≤_ to _≤ℕ_)

import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix
  as CrossMatrix
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
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
-- Upstream operator witness surface.
--
-- The weighted Schur theorem currently exports only operator-norm targets, not
-- the operator/pairing/quadratic-form data needed by Blocker 2A. This record
-- is the minimal upstream witness that would make the Stage 3 operator concrete
-- at the weighted-Schur boundary itself.

record WeightedSchurMatrixOperatorData
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkWeightedSchurMatrixOperatorData
  field
    weightedSchurOperator :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex

    absWeakPairing :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex →
      Nat

    absQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    weakQuadraticFormConstant : Nat

    absQuadraticFormDef :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≡
        absWeakPairing (weightedSchurOperator x) x

    weightedSchurControlsQuadratic :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≤ℕ
        weakQuadraticFormConstant
          *ℕ ResidueNorm.weakNormSquared residueNormModel shellIndex x

    operatorRealizesWeightedSchurFrontier : Set

open WeightedSchurMatrixOperatorData public

record WeightedSchurOperatorWitness
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkWeightedSchurOperatorWitness
  field
    weightedSchurOperator :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex

    absWeakPairing :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex →
      Nat

    absQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    weakQuadraticFormConstant : Nat

    absQuadraticFormDef :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≡
        absWeakPairing (weightedSchurOperator x) x

    weightedSchurControlsQuadratic :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≤ℕ
        weakQuadraticFormConstant
          *ℕ ResidueNorm.weakNormSquared residueNormModel shellIndex x

    witnessClosed : Bool

fromWeightedSchurMatrixOperatorData :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  WeightedSchurMatrixOperatorData residueNormModel shellIndex →
  WeightedSchurOperatorWitness residueNormModel shellIndex
fromWeightedSchurMatrixOperatorData datum =
  mkWeightedSchurOperatorWitness
    (WeightedSchurMatrixOperatorData.weightedSchurOperator datum)
    (WeightedSchurMatrixOperatorData.absWeakPairing datum)
    (WeightedSchurMatrixOperatorData.absQuadraticForm datum)
    (WeightedSchurMatrixOperatorData.weakQuadraticFormConstant datum)
    (WeightedSchurMatrixOperatorData.absQuadraticFormDef datum)
    (WeightedSchurMatrixOperatorData.weightedSchurControlsQuadratic datum)
    false

fromProfileCrossMatrixKernelData :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  CrossMatrix.ProfileCrossMatrixKernelData residueNormModel shellIndex →
  WeightedSchurMatrixOperatorData residueNormModel shellIndex
fromProfileCrossMatrixKernelData datum =
  mkWeightedSchurMatrixOperatorData
    (CrossMatrix.ProfileCrossMatrixKernelData.weightedSchurOperator datum)
    (CrossMatrix.ProfileCrossMatrixKernelData.absWeakPairing datum)
    (CrossMatrix.ProfileCrossMatrixKernelData.absQuadraticForm datum)
    (CrossMatrix.ProfileCrossMatrixKernelData.weakQuadraticFormConstant datum)
    (CrossMatrix.ProfileCrossMatrixKernelData.absQuadraticFormDef datum)
    (CrossMatrix.ProfileCrossMatrixKernelData.profileCrossMatrixControlsQuadratic datum)
    (CrossMatrix.ProfileCrossMatrixKernelData.kernelRealizesProfileCrossProductMatrix datum)

UnitShellWeightedSchurOperatorWitnessTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
UnitShellWeightedSchurOperatorWitnessTarget residueNormModel =
  WeightedSchurOperatorWitness residueNormModel (suc zero)

UnitShellWeightedSchurMatrixOperatorDataTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
UnitShellWeightedSchurMatrixOperatorDataTarget residueNormModel =
  WeightedSchurMatrixOperatorData residueNormModel (suc zero)

weightedSchurOperatorWitnessClosed : Bool
weightedSchurOperatorWitnessClosed = false

weightedSchurOperatorWitnessClosedIsFalse :
  weightedSchurOperatorWitnessClosed ≡ false
weightedSchurOperatorWitnessClosedIsFalse = refl

actualUnitShellWeightedSchurOperatorWitnessClosed : Bool
actualUnitShellWeightedSchurOperatorWitnessClosed =
  weightedSchurOperatorWitnessClosed

actualUnitShellWeightedSchurOperatorWitnessClosedIsFalse :
  actualUnitShellWeightedSchurOperatorWitnessClosed ≡ false
actualUnitShellWeightedSchurOperatorWitnessClosedIsFalse = refl

weightedSchurMatrixOperatorDataClosed : Bool
weightedSchurMatrixOperatorDataClosed =
  CrossMatrix.actualUnitShellProfileCrossMatrixKernelDataClosed

weightedSchurMatrixOperatorDataClosedIsFalse :
  weightedSchurMatrixOperatorDataClosed ≡ false
weightedSchurMatrixOperatorDataClosedIsFalse =
  CrossMatrix.actualUnitShellProfileCrossMatrixKernelDataClosedIsFalse

actualUnitShellWeightedSchurMatrixOperatorDataClosed : Bool
actualUnitShellWeightedSchurMatrixOperatorDataClosed =
  weightedSchurMatrixOperatorDataClosed

actualUnitShellWeightedSchurMatrixOperatorDataClosedIsFalse :
  actualUnitShellWeightedSchurMatrixOperatorDataClosed ≡ false
actualUnitShellWeightedSchurMatrixOperatorDataClosedIsFalse = refl

------------------------------------------------------------------------
-- Proof-derived gate definitions.

weightedSchurProductBoundClosed : Bool
weightedSchurProductBoundClosed with CrossMatrix.canonicalProfileCrossProductMatrix
... | _ = true

weightedSchurProductBoundClosedIsTrue :
  weightedSchurProductBoundClosed ≡ true
weightedSchurProductBoundClosedIsTrue = refl
