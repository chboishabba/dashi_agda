module DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorResultValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorResultExact as Target

validationDiscoveryTailCount : Target.discoveryTwoSidedTailCount ≡ 7074
validationDiscoveryTailCount = refl

validationHeldOutTailCount : Target.heldOutTwoSidedTailCount ≡ 10449
validationHeldOutTailCount = refl

validationHeldOutDoesNotPromoteMonster :
  Target.addressDiscriminatorPromotesMonster
    Target.canonicalAddressDiscriminatorResultBoundary
  ≡ false
validationHeldOutDoesNotPromoteMonster = refl

validationBothWindowsNonExtreme :
  Target.bothWindowsNonExtreme
    Target.canonicalAddressDiscriminatorResultBoundary
  ≡ true
validationBothWindowsNonExtreme = refl
