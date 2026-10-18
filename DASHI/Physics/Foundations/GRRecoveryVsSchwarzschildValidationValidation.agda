{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRRecoveryVsSchwarzschildValidationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.GRRecoveryVsSchwarzschildValidationExact as G

schwarzschildNotGenericPremise :
  G.schwarzschildRadialValuationRequiredForGenericAttachment ≡ false
schwarzschildNotGenericPremise = refl

knownLimitStillRequired :
  G.schwarzschildWeakFieldValidationStillPhysicallyRequired ≡ true
knownLimitStillRequired = refl
