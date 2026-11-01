{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricFiniteTangentBasisFromCarrierEqualityTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.CMP119SymmetricFiniteTangentBasisFromCarrierEqualityExact as C

noTenIndependentChoices : C.tenIndependentFiniteTangentChoicesRequired ≡ false
noTenIndependentChoices = refl

onlyReferenceBackground :
  C.onlyReferenceBackgroundRemainsAfterTenSlotCarrierChoice ≡ true
onlyReferenceBackground = refl
