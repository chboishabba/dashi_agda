module DASHI.Physics.YangMills.YMClayF1PhysicalMinCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayF1PhysicalMinCutExact as F1

fullR339MagnitudeEqualityIsNotPrimitive :
  F1.fullR339MagnitudeEqualityPrimitive ≡ false
fullR339MagnitudeEqualityIsNotPrimitive =
  F1.fullR339MagnitudeEqualityPrimitiveIsFalse

r343ConfirmsWeakerConsumer :
  F1.r343ConfirmsMagnitudeEqualityNotPrimitive ≡ false
r343ConfirmsWeakerConsumer = F1.fullR339MagnitudeEqualityPrimitiveIsFalse

sharedMarkedWeakRouteIsAvailable :
  F1.r344R346SharedMarkedRouteAvailable ≡ true
sharedMarkedWeakRouteIsAvailable =
  F1.r344R346SharedMarkedRouteAvailableIsTrue

independentWilsonR295CarrierEqualityIsNotPrimitive :
  F1.independentWilsonR295CarrierEqualityPrimitive ≡ false
independentWilsonR295CarrierEqualityIsNotPrimitive = refl

f1BResidueIsTypedR315Presentation :
  F1.f1BPhysicalResidueIsR315Presentation ≡ true
f1BResidueIsTypedR315Presentation = refl
