{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB4PhysicalR440ExistentialTargetTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSCanonicalB4PhysicalR440ExistentialTargetExact as T

allPairsSelectorFixed : T.b4ExistentialTargetUsesAllPairsSelector ≡ true
allPairsSelectorFixed = T.b4ExistentialTargetUsesAllPairsSelectorIsTrue

coreMassPositivityDerived : T.b4CoreCompanionNonnegativeDerived ≡ true
coreMassPositivityDerived = T.b4CoreCompanionNonnegativeDerivedIsTrue

localEDPositivityDerived : T.b4AllPairsLocalEDNonnegativeDerived ≡ true
localEDPositivityDerived = T.b4AllPairsLocalEDNonnegativeDerivedIsTrue

onlyConstantsRemainQuantitative : T.b4OnlyThetaAndEDCoefficientRemainQuantitativeWitnesses ≡ true
onlyConstantsRemainQuantitative = T.b4OnlyThetaAndEDCoefficientRemainQuantitativeWitnessesIsTrue

keyLemmaStillOpen : T.b4ExistentialUniformPhysicalR440PaymentClosed ≡ false
keyLemmaStillOpen = T.b4ExistentialUniformPhysicalR440PaymentClosedIsFalse
