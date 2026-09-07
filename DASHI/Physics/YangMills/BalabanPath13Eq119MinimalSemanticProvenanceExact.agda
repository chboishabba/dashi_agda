{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119MinimalSemanticProvenanceExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): MINIMAL-SEMANTIC PROVENANCE / FRONTIER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record MinimalSemanticRouteStatus : Set where
  field
    preferredRouteUsesMinimalSemanticCalculus : Bool
    historicalR177Compatibility : Bool
    historicalR159Compatibility : Bool

    dexpJminusPairConstructed : Bool
    reducedAdjointExpFamilyConstructed : Bool

    selectedPhysicalRepresentationConstructed : Bool
    bishopToLegacyBridgeConstructed : Bool
    cutThresholdConstructed : Bool
    physicalEq119Closed : Bool
open MinimalSemanticRouteStatus public

canonicalMinimalSemanticRouteStatus : MinimalSemanticRouteStatus
canonicalMinimalSemanticRouteStatus = record
  { preferredRouteUsesMinimalSemanticCalculus = true
  ; historicalR177Compatibility = true
  ; historicalR159Compatibility = true
  ; dexpJminusPairConstructed = false
  ; reducedAdjointExpFamilyConstructed = false
  ; selectedPhysicalRepresentationConstructed = false
  ; bishopToLegacyBridgeConstructed = false
  ; cutThresholdConstructed = false
  ; physicalEq119Closed = false
  }

preferredRouteUsesMinimalSemanticCalculusIsTrue :
  preferredRouteUsesMinimalSemanticCalculus canonicalMinimalSemanticRouteStatus ≡ true
preferredRouteUsesMinimalSemanticCalculusIsTrue = refl

dexpJminusPairConstructedIsFalse :
  dexpJminusPairConstructed canonicalMinimalSemanticRouteStatus ≡ false
dexpJminusPairConstructedIsFalse = refl

reducedAdjointExpFamilyConstructedIsFalse :
  reducedAdjointExpFamilyConstructed canonicalMinimalSemanticRouteStatus ≡ false
reducedAdjointExpFamilyConstructedIsFalse = refl

physicalEq119ClosedIsFalse :
  physicalEq119Closed canonicalMinimalSemanticRouteStatus ≡ false
physicalEq119ClosedIsFalse = refl

cmp98Path13MinimalSemanticProvenanceLevel : ProofLevel
cmp98Path13MinimalSemanticProvenanceLevel = machineChecked
