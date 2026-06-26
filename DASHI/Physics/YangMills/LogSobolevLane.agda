module DASHI.Physics.YangMills.LogSobolevLane where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives

record LogSobolevLane : Set₁ where
  field
    configSpaceDefined : Bool
    measureDefined : Bool
    lsiConstantBounded : Bool
    hypercontractivityFollows : Bool
    spectralGapFollows : Bool
    bridgeToPhysicalGap : Bool
    configSpaceDefinedIsFalse : configSpaceDefined ≡ false
    measureDefinedIsFalse : measureDefined ≡ false
    lsiConstantBoundedIsFalse : lsiConstantBounded ≡ false
    hypercontractivityFollowsIsFalse : hypercontractivityFollows ≡ false
    spectralGapFollowsIsFalse : spectralGapFollows ≡ false
    bridgeToPhysicalGapIsFalse : bridgeToPhysicalGap ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalLogSobolevLane : LogSobolevLane
canonicalLogSobolevLane = record
  { configSpaceDefined = false
  ; measureDefined = false
  ; lsiConstantBounded = false
  ; hypercontractivityFollows = false
  ; spectralGapFollows = false
  ; bridgeToPhysicalGap = false
  ; configSpaceDefinedIsFalse = refl
  ; measureDefinedIsFalse = refl
  ; lsiConstantBoundedIsFalse = refl
  ; hypercontractivityFollowsIsFalse = refl
  ; spectralGapFollowsIsFalse = refl
  ; bridgeToPhysicalGapIsFalse = refl
  ; noClayPromotion = refl
  }
