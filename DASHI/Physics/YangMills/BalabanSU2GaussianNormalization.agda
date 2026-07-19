module DASHI.Physics.YangMills.BalabanSU2GaussianNormalization where

open import Agda.Builtin.Equality using (_≡_)

record GaussianNormalization (Scalar : Set) : Set₁ where
  field
    determinant normalization inverseDeterminant : Scalar
    multiply : Scalar → Scalar → Scalar
    Positive : Scalar → Set
    determinantPositive : Positive determinant
    normalizationPositive : Positive normalization
    normalizationSquare : multiply normalization normalization ≡ inverseDeterminant

open GaussianNormalization public
