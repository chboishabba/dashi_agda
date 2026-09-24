{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenNormalizedTargetEqualityValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119TenNormalizedTargetEqualityExact as T

noSecondTensorTheorem :
  T.additionalTensorTheoremAfterTenTargetEqualitiesRequired ≡ false
noSecondTensorTheorem = refl
