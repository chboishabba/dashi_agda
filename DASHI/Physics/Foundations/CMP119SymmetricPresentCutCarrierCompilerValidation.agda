{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as C

r144CarrierBuiltWithTenSlotTangent :
  C.r144CompatibleTenSlotCarrierBuiltByConstruction ≡ true
r144CarrierBuiltWithTenSlotTangent = refl

noPostHocR250R144Equality :
  C.postHocR250ToR144CarrierEqualityRequired ≡ false
noPostHocR250R144Equality = refl
