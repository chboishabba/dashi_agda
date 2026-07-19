module DASHI.Physics.YangMills.BalabanSU2PolarizationFourier where

open import Agda.Builtin.Equality using (_≡_)

record FourierPolarization (Direction Momentum Scalar : Set) : Set₁ where
  field
    transformDirection : Momentum → Direction → Direction
    tensor : Direction → Direction → Scalar
    momentumTensor : Momentum → Direction → Direction → Scalar
    transformDefinition :
      ∀ momentum left right →
      momentumTensor momentum left right
        ≡ tensor (transformDirection momentum left)
            (transformDirection momentum right)

    transverseTensor remainderTensor : Momentum → Direction → Direction → Scalar
    add : Scalar → Scalar → Scalar
    decomposition :
      ∀ momentum left right →
      momentumTensor momentum left right
        ≡ add (transverseTensor momentum left right)
            (remainderTensor momentum left right)

open FourierPolarization public
