module DASHI.Physics.CondensedMatter.MATBGEntropyCombinatorics2026Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.CondensedMatter.MATBGEntropyCombinatorics2026Exact as Entropy

highTCountAtFilling0 : Entropy.highTemperatureMicrostates Entropy.filling0 ≡ 70
highTCountAtFilling0 = refl

highTCountAtFilling1 : Entropy.highTemperatureMicrostates Entropy.filling1 ≡ 56
highTCountAtFilling1 = refl

highTCountAtFilling2 : Entropy.highTemperatureMicrostates Entropy.filling2 ≡ 28
highTCountAtFilling2 = refl

highTCountAtFilling3 : Entropy.highTemperatureMicrostates Entropy.filling3 ≡ 8
highTCountAtFilling3 = refl

lowTCountAtFilling0 : Entropy.lowTemperatureMicrostates Entropy.filling0 ≡ 1
lowTCountAtFilling0 = refl

lowTCountAtFilling1 : Entropy.lowTemperatureMicrostates Entropy.filling1 ≡ 4
lowTCountAtFilling1 = refl

lowTCountAtFilling2 : Entropy.lowTemperatureMicrostates Entropy.filling2 ≡ 6
lowTCountAtFilling2 = refl

lowTCountAtFilling3 : Entropy.lowTemperatureMicrostates Entropy.filling3 ≡ 4
lowTCountAtFilling3 = refl

cnpLowTemperatureCountImpliesLogOneTarget : Entropy.lowTemperatureMicrostates Entropy.filling0 ≡ 1
cnpLowTemperatureCountImpliesLogOneTarget = refl

microstateCountsDoNotCreateSameSampleQTM : Entropy.sameSampleQTMEntropyPaid Entropy.canonicalEntropyCombinatoricsBoundary ≡ false
microstateCountsDoNotCreateSameSampleQTM = refl
