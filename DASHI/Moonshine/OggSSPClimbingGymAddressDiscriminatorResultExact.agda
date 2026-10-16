module DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorResultExact where

------------------------------------------------------------------------
-- RESULT RECEIPT FOR THE PREDECLARED NATIVE-ADDRESS DISCRIMINATOR
--
-- Design owner:
--   OggSSPClimbingGymAddressDiscriminatorExact
-- Executable producer:
--   scripts/monster_climbing_gym_address_discriminator.py
--
-- The single predeclared depth-one statistic is standardized independently
-- within each prime against its one-cell-period boundary-shift null, then the
-- 15-vs-5 Ogg/control mean-z contrast is ranked against every C(20,5)=15504
-- balanced relabelling.
--
-- Discovery (zeros 1..849):
--   actual contrast = -0.4278031863...
--   two-sided rank  = 7074 / 15504  (~45.63%)
--
-- Held out (zeros 850..1698):
--   actual contrast = +0.2351561178...
--   two-sided rank  = 10449 / 15504 (~67.40%)
--
-- Thus the stronger native-address observable also supplies no Ogg-specific
-- anomaly on either window.  This owner records only the finite numerical
-- receipt and promotion boundary; it does not turn a null result into a
-- theorem about the Monster group or zeta zeros.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorExact as Design

balancedAssignmentCount : Nat
balancedAssignmentCount = 15504

discoveryZeroCount : Nat
discoveryZeroCount = 849

heldOutZeroCount : Nat
heldOutZeroCount = 849

discoveryTwoSidedTailCount : Nat
discoveryTwoSidedTailCount = 7074

heldOutTwoSidedTailCount : Nat
heldOutTwoSidedTailCount = 10449

discoveryContrastLabel : String
discoveryContrastLabel = "-0.4278031863279293"

heldOutContrastLabel : String
heldOutContrastLabel = "0.23515611780682538"

producerPath : String
producerPath = "scripts/monster_climbing_gym_address_discriminator.py"

resultRegressionPath : String
resultRegressionPath = "scripts/test_monster_climbing_gym_address_discriminator_result.py"

record AddressDiscriminatorResultBoundary : Set where
  constructor address-discriminator-result-boundary
  field
    predeclaredDesignReused : Bool
    discoveryWindowEvaluated : Bool
    heldOutWindowEvaluated : Bool
    allBalancedAssignmentsUsedInBothWindows : Bool
    bothWindowsNonExtreme : Bool
    addressDiscriminatorPromotesMonster : Bool
    addressDiscriminatorPromotesMoonshineMechanism : Bool
    addressDiscriminatorPromotesRiemannHypothesis : Bool
    nullResultCreatesUniversalNoGoTheorem : Bool

open AddressDiscriminatorResultBoundary public

canonicalAddressDiscriminatorResultBoundary : AddressDiscriminatorResultBoundary
canonicalAddressDiscriminatorResultBoundary =
  address-discriminator-result-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false

predeclaredDepthStillOne : Design.depth Design.canonicalAddressDiscriminatorDesign ≡ 1
predeclaredDepthStillOne = refl

predeclaredMultipleStatisticSearchStillForbidden :
  Design.multipleStatisticSearchAllowed Design.canonicalAddressDiscriminatorDesign
  ≡ false
predeclaredMultipleStatisticSearchStillForbidden = refl
