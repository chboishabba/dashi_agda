module DASHI.Moonshine.Y443SelectedNativeModeOneGriessExact where

------------------------------------------------------------------------
-- M01: THE GRIESS FIRST PRODUCT ON THE ACTUAL SELECTED ORBIFOLD.
--
-- Source of every equation below is the selected, already-existing
-- VN.VNaturalConstruction.Vnatural, NOT a duplicate abstract algebra.
-- There is NO arbitrary independent firstProduct: its value is forced
-- to be the unique grade-two preimage of the ORIGINAL VOA mode at +1.
--
-- In a genuine CFT-type VOA with V_1=0, VOA skew symmetry plus the
-- translation/vacuum laws give commutativity of the weight-two product.
-- Those source identities are NOT proof fields in the current weak core.
-- The commutativity/bilinearity witnesses therefore remain explicit.
--
-- The result below genuinely *constructs* the preexisting
-- Y443FLMGriessFullAutSelectedVOAExact.ConcreteGriessProduct from these
-- original-source laws; it does not create an unrelated algebra.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.Y443FLMGriessFullAutSelectedVOAExact as FLM

module Selected (construction : VN.VNaturalConstruction) where
  originalVOA : VOA.VertexOperatorAlgebra
  originalVOA = VN.VNaturalConstruction.Vnatural construction

  module S = FLM.Selected originalVOA

  record SourceNativeGriessLaws : Setω where
    field
      -- Original weight-two mode +1 CLOSURE, with a unique preimage.
      modeOneGradeTwo : S.WeightTwo → S.WeightTwo → S.WeightTwo
      modeOneReallyOriginal : (x y : S.WeightTwo) →
        S.include (modeOneGradeTwo x y)
        ≡ VOA.VertexOperatorData.mode S.Y
          (S.include x) (+ 1) (S.include y)

      includeIsInjective : (x y : S.WeightTwo) →
        S.include x ≡ S.include y → x ≡ y

      -- Grade-two operations come from the SAME selected graded module.
      additionOnGradeTwo : S.WeightTwo → S.WeightTwo → S.WeightTwo
      scalarOnGradeTwo : S.Scalar → S.WeightTwo → S.WeightTwo
      actualAddition : (x y : S.WeightTwo) →
        S.include (additionOnGradeTwo x y)
        ≡ VOA.GradedModule._+_ S.GM (S.include x) (S.include y)
      actualScaling : (s : S.Scalar) (x : S.WeightTwo) →
        S.include (scalarOnGradeTwo s x)
        ≡ VOA.GradedModule._·_ S.GM s (S.include x)

      selectedConformalGradeTwo : S.WeightTwo
      conformalReallyOriginal :
        S.include selectedConformalGradeTwo
        ≡ VOA.VertexOperatorData.conformalVector S.Y

      -- M01 claims these laws for the genuine selected mode-one source;
      -- an arbitrary dimension or C3 character cannot prove them.
      modeOneCommutative : (x y : S.WeightTwo) →
        modeOneGradeTwo x y ≡ modeOneGradeTwo y x
      modeOneLeftLinear : (x y z : S.WeightTwo) →
        modeOneGradeTwo (additionOnGradeTwo x y) z
        ≡ additionOnGradeTwo
          (modeOneGradeTwo x z) (modeOneGradeTwo y z)
      modeOneScalarLinear : (s : S.Scalar) (x y : S.WeightTwo) →
        modeOneGradeTwo (scalarOnGradeTwo s x) y
        ≡ scalarOnGradeTwo s (modeOneGradeTwo x y)

  open SourceNativeGriessLaws public

  -- Not a new picked algebra: this is the *actual mode-one* algebra.
  actualSelectedGriess : SourceNativeGriessLaws →
    S.ConcreteGriessProduct
  actualSelectedGriess laws = record
    { S.firstProduct = modeOneGradeTwo laws
    ; S.conformalWeightTwo = selectedConformalGradeTwo laws
    ; S.conformalIsActual = conformalReallyOriginal laws
    ; S.weightTwoAdd = additionOnGradeTwo laws
    ; S.weightTwoScale = scalarOnGradeTwo laws
    ; S.includeWeightTwoAdd = actualAddition laws
    ; S.includeWeightTwoScale = actualScaling laws
    ; S.firstProductIsModeOne = modeOneReallyOriginal laws
    ; S.gradeEmbeddingInjective = includeIsInjective laws
    }

  selectedModeOneIsCommutative :
    (laws : SourceNativeGriessLaws) (x y : S.WeightTwo) →
    S.firstProduct (actualSelectedGriess laws) x y
    ≡ S.firstProduct (actualSelectedGriess laws) y x
  selectedModeOneIsCommutative laws x y =
    modeOneCommutative laws x y

  selectedModeOneIsLeftLinear :
    (laws : SourceNativeGriessLaws) (x y z : S.WeightTwo) →
    S.firstProduct (actualSelectedGriess laws)
      (S.weightTwoAdd (actualSelectedGriess laws) x y) z
    ≡ S.weightTwoAdd (actualSelectedGriess laws)
        (S.firstProduct (actualSelectedGriess laws) x z)
        (S.firstProduct (actualSelectedGriess laws) y z)
  selectedModeOneIsLeftLinear laws x y z =
    modeOneLeftLinear laws x y z
