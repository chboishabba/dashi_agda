{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119SplitCalculusProvenanceExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): SPLIT-CALCULUS PROVENANCE / FRONTIER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SplitCalculusRouteStatus : Set where
  field
    preferredRouteUsesSplitCalculus : Bool
    historicalUniformCalculusCompatibility : Bool
    historicalR177Compatibility : Bool

    expLogDifferentialConstructed : Bool
    adjointExpRealizationConstructed : Bool

    selectedPhysicalRepresentationConstructed : Bool
    bishopToLegacyBridgeConstructed : Bool
    cutThresholdConstructed : Bool
    physicalEq119Closed : Bool
open SplitCalculusRouteStatus public

canonicalSplitCalculusRouteStatus : SplitCalculusRouteStatus
canonicalSplitCalculusRouteStatus = record
  { preferredRouteUsesSplitCalculus = true
  ; historicalUniformCalculusCompatibility = true
  ; historicalR177Compatibility = true
  ; expLogDifferentialConstructed = false
  ; adjointExpRealizationConstructed = false
  ; selectedPhysicalRepresentationConstructed = false
  ; bishopToLegacyBridgeConstructed = false
  ; cutThresholdConstructed = false
  ; physicalEq119Closed = false
  }

preferredRouteUsesSplitCalculusIsTrue :
  preferredRouteUsesSplitCalculus canonicalSplitCalculusRouteStatus ≡ true
preferredRouteUsesSplitCalculusIsTrue = refl

expLogDifferentialConstructedIsFalse :
  expLogDifferentialConstructed canonicalSplitCalculusRouteStatus ≡ false
expLogDifferentialConstructedIsFalse = refl

adjointExpRealizationConstructedIsFalse :
  adjointExpRealizationConstructed canonicalSplitCalculusRouteStatus ≡ false
adjointExpRealizationConstructedIsFalse = refl

physicalEq119ClosedIsFalse :
  physicalEq119Closed canonicalSplitCalculusRouteStatus ≡ false
physicalEq119ClosedIsFalse = refl

cmp98Path13SplitCalculusProvenanceLevel : ProofLevel
cmp98Path13SplitCalculusProvenanceLevel = machineChecked
