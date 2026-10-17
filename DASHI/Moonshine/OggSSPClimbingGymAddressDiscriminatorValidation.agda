module DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorExact as Discriminator

------------------------------------------------------------------------
-- RED-first contract for the predeclared address-space falsification test.
------------------------------------------------------------------------

primeLocalShiftNullRequired :
  Discriminator.perPrimeShiftNullRequired
    Discriminator.canonicalAddressDiscriminatorBoundary
  ≡ true
primeLocalShiftNullRequired = refl

labelPermutationRequired :
  Discriminator.exhaustiveBalancedLabelPermutationRequired
    Discriminator.canonicalAddressDiscriminatorBoundary
  ≡ true
labelPermutationRequired = refl

noMonsterPromotionFromExploratoryTail :
  Discriminator.addressStatisticAlonePromotesMonsterMechanism
    Discriminator.canonicalAddressDiscriminatorBoundary
  ≡ false
noMonsterPromotionFromExploratoryTail = refl
