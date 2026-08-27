module DASHI.Governance.CapabilityFunctioningNonDescentExact where

------------------------------------------------------------------------
-- CAPABILITY / FUNCTIONING NON-DESCENT
--
-- SOURCE CALIBRATION
-- Amartya Sen, Commodities and Capabilities, North-Holland, 1985.
-- ISBN 9780444877307. No DOI asserted for the book.
-- Amartya Sen, Development as Freedom, Alfred A. Knopf, 1999.
-- ISBN 9780375406195. No DOI asserted for the book.
--
-- Sen motivates the capability/functioning distinction. The finite option-set
-- witnesses and factorisation theorems below are DASHI constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.OptionConeCoercionExact as Cone

record CapabilityFunctioningSystem (State Option : Set) : Set₁ where
  constructor capability-functioning-system
  field
    reachability : Cone.SafeReachabilitySystem State Option
    Functioning : State → Option

open CapabilityFunctioningSystem public

data DemoState : Set where
  wideSameAction narrowSameAction wideOtherAction : DemoState

data DemoOption : Set where
  remain leave recover : DemoOption

data DemoAvailable : DemoState → DemoOption → Set where
  wideRemain : DemoAvailable wideSameAction remain
  wideLeave : DemoAvailable wideSameAction leave
  wideRecover : DemoAvailable wideSameAction recover
  narrowRemain : DemoAvailable narrowSameAction remain
  otherRemain : DemoAvailable wideOtherAction remain
  otherLeave : DemoAvailable wideOtherAction leave
  otherRecover : DemoAvailable wideOtherAction recover

demoReachability : Cone.SafeReachabilitySystem DemoState DemoOption
demoReachability = Cone.safeReachabilitySystem DemoAvailable

functioning : DemoState → DemoOption
functioning wideSameAction = remain
functioning narrowSameAction = remain
functioning wideOtherAction = leave

capabilitySignature : DemoState → Bool
capabilitySignature wideSameAction = true
capabilitySignature narrowSameAction = false
capabilitySignature wideOtherAction = true

sameFunctioningDifferentCapability :
  INF.NonFactorabilityWitness functioning capabilitySignature
sameFunctioningDifferentCapability =
  INF.nonFactorabilityWitness wideSameAction narrowSameAction refl (λ ())

sameCapabilityDifferentFunctioning :
  INF.NonFactorabilityWitness capabilitySignature functioning
sameCapabilityDifferentFunctioning =
  INF.nonFactorabilityWitness wideSameAction wideOtherAction refl (λ ())

functioningCannotRecoverCapability :
  INF.FactorsThrough functioning capabilitySignature → ⊥
functioningCannotRecoverCapability =
  INF.witnessRulesOutEveryFlatFactorisation sameFunctioningDifferentCapability

capabilityCannotRecoverFunctioning :
  INF.FactorsThrough capabilitySignature functioning → ⊥
capabilityCannotRecoverFunctioning =
  INF.witnessRulesOutEveryFlatFactorisation sameCapabilityDifferentFunctioning

record RepairStageBoundary : Set where
  constructor repair-stage-boundary
  field
    canModifyEqualsModificationAttempted : Bool
    canModifyEqualsModificationAttemptedIsFalse :
      canModifyEqualsModificationAttempted ≡ false
    attemptedEqualsEffective : Bool
    attemptedEqualsEffectiveIsFalse : attemptedEqualsEffective ≡ false
    effectiveEqualsCapabilityExpanded : Bool
    effectiveEqualsCapabilityExpandedIsFalse :
      effectiveEqualsCapabilityExpanded ≡ false
    capabilityExpandedEqualsDesiredFunctioning : Bool
    capabilityExpandedEqualsDesiredFunctioningIsFalse :
      capabilityExpandedEqualsDesiredFunctioning ≡ false

canonicalRepairStageBoundary : RepairStageBoundary
canonicalRepairStageBoundary =
  repair-stage-boundary false refl false refl false refl false refl
