module DASHI.Moonshine.Y443NativeModeOneBilinearWeldExact where

-- Consume the actual selected mode-one laws, rather than asking the
-- selected source to furnish a second independent bilinearity record.
-- No assumption of product agreement or FLM identity is introduced.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.Y443SelectedNativeModeOneGriessExact as Native
import DASHI.Moonshine.Y443FLMBilinearProductSpanWeldExact as Weld
import DASHI.Moonshine.Y443FLMWeightTwoBasisUVExact as Basis

module Selected (construction : VN.VNaturalConstruction) where
  module N = Native.Selected construction
  module W = Weld.Selected N.originalVOA
  open Basis using (sym; trans; cong; cong₂)

  module WithLaws (laws : N.SourceNativeGriessLaws) where
    module L = W.WithSpan (N.actualSelectedGriess laws)
    open N using (modeOneGradeTwo; additionOnGradeTwo; scalarOnGradeTwo;
      modeOneCommutative; modeOneLeftLinear; modeOneScalarLinear)

    product = modeOneGradeTwo laws
    add = additionOnGradeTwo laws
    scale = scalarOnGradeTwo laws

    rightAdd : (x y z : N.S.WeightTwo) →
      product x (add y z) ≡ add (product x y) (product x z)
    rightAdd x y z =
      trans (modeOneCommutative laws x (add y z))
        (trans (modeOneLeftLinear laws y z x)
          (cong₂ add (modeOneCommutative laws y x)
                     (modeOneCommutative laws z x)))

    rightScale : (s : N.S.Scalar) (x y : N.S.WeightTwo) →
      product x (scale s y) ≡ scale s (product x y)
    rightScale s x y =
      trans (modeOneCommutative laws x (scale s y))
        (trans (modeOneScalarLinear laws s y x)
          (cong (scale s) (modeOneCommutative laws y x)))

    module WithActualSpan (span : L.L.ActualWeightTwoSpan) where
      module C = L.Compare span N.S.WeightTwo add scale

      nativeBilinear : C.Bilinear product
      nativeBilinear = record
        { linearLeft = λ y → record
          { sumLaw = λ x z → modeOneLeftLinear laws x z y
          ; scaleLaw = λ s x → modeOneScalarLinear laws s x y
          }
        ; linearRight = λ x → record
          { sumLaw = rightAdd x
          ; scaleLaw = λ s y → rightScale s x y
          }
        }
