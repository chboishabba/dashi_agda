{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GRAnchoredStressWeldCompilerValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.GRAnchoredSharedEffectiveSourceExact as G
import DASHI.Physics.Foundations.CMP119GRAnchoredStressWeldCompilerExact as C

grFactorisationIsDefinitional :
  G.grFactorisationIsPrimitiveOnGRAnchoredRoute ≡ false
grFactorisationIsDefinitional = refl

crossSectorEqualityRemains :
  C.crossSectorGRToCMP119StressEqualityRequired ≡ true
crossSectorEqualityRemains = refl
