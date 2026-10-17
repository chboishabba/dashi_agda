{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB4PhysicalR440LiteralUniformTargetTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSCanonicalB4PhysicalR440LiteralUniformTargetExact as T

literalSignedR440 : T.b4LiteralTargetFixesSignedR440Work ≡ true
literalSignedR440 = T.b4LiteralTargetFixesSignedR440WorkIsTrue

literalCoreMass : T.b4LiteralTargetFixesCoreCompanionMass ≡ true
literalCoreMass = T.b4LiteralTargetFixesCoreCompanionMassIsTrue

literalLocalED : T.b4LiteralTargetFixesSelectedPairLocalED ≡ true
literalLocalED = T.b4LiteralTargetFixesSelectedPairLocalEDIsTrue

selectorFamilyFixed : T.b4LiteralTargetUsesOneFixedSelectorPerFamily ≡ true
selectorFamilyFixed = T.b4LiteralTargetUsesOneFixedSelectorPerFamilyIsTrue

uniformConstants : T.b4LiteralTargetThetaAndCoefficientUniformAcrossPhysicalSystems ≡ true
uniformConstants = T.b4LiteralTargetThetaAndCoefficientUniformAcrossPhysicalSystemsIsTrue

viscosityExplicit : T.b4LiteralTargetRequiresNonnegativeViscosity ≡ true
viscosityExplicit = T.b4LiteralTargetRequiresNonnegativeViscosityIsTrue

massPositive : T.b4LiteralTargetRequiresCoreMassNonnegative ≡ true
massPositive = T.b4LiteralTargetRequiresCoreMassNonnegativeIsTrue

edPositive : T.b4LiteralTargetRequiresLocalEDNonnegative ≡ true
edPositive = T.b4LiteralTargetRequiresLocalEDNonnegativeIsTrue

keyLemmaOpen : T.b4LiteralUniformPhysicalR440PaymentClosed ≡ false
keyLemmaOpen = T.b4LiteralUniformPhysicalR440PaymentClosedIsFalse
