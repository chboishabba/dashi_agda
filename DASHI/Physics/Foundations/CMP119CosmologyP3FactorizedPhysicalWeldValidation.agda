{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3FactorizedPhysicalWeldValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP3FactorizedPhysicalWeldExact as P3

q3NoLongerIndependentSourcePackage :
  P3.q3IndependentSourcePackageStillRequired ≡ false
q3NoLongerIndependentSourcePackage = refl

fixedStateWeldMakesStateIdentityDefinitional :
  P3.sameFiniteStateCarrierIsDefinitional ≡ true
fixedStateWeldMakesStateIdentityDefinitional = refl

factorizedErrorPaysFiniteBridge :
  P3.factorizedDensityErrorPaysQ3Bridge ≡ true
factorizedErrorPaysFiniteBridge = refl

remainingPaymentIsExistingPhysicalHaarWeld :
  P3.remainingPaymentIsExistingPhysicalHaarQuadratureSemantics ≡ true
remainingPaymentIsExistingPhysicalHaarWeld = refl
