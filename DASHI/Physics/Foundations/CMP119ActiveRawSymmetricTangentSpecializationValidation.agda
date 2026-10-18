{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ActiveRawSymmetricTangentSpecializationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119ActiveRawSymmetricTangentSpecializationExact as S

tenSlotMapDefinitional :
  S.tenSlotToFiniteTangentMapIsDefinitional ≡ true
tenSlotMapDefinitional = refl

noTenArbitraryVectors :
  S.tenArbitraryFiniteTangentChoicesStillRequired ≡ false
noTenArbitraryVectors = refl
