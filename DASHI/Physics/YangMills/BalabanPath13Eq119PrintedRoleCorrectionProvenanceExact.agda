{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119PrintedRoleCorrectionProvenanceExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): PRINTED-ROLE CORRECTION / PROVENANCE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record PrintedRoleCorrectionStatus : Set where
  field
    r148PrintedOuterIsDexpPlus : Bool
    r148PrintedPointInverseIsJplus : Bool
    printedAdjointIsAdjointExp : Bool

    oldDirectMinusJminusRouteTypeCompatible : Bool
    oldDirectMinusJminusRouteSourcePreferred : Bool

    correctedPrintedRoleRoutePreferred : Bool
    correctedRouteRequiresGlobalAdjointInverse : Bool

    selectedPhysicalRepresentationConstructed : Bool
    bishopToLegacyBridgeConstructed : Bool
    printedOperatorSemanticsConstructed : Bool
    cutThresholdConstructed : Bool
    physicalEq119Closed : Bool
open PrintedRoleCorrectionStatus public

canonicalPrintedRoleCorrectionStatus : PrintedRoleCorrectionStatus
canonicalPrintedRoleCorrectionStatus = record
  { r148PrintedOuterIsDexpPlus = true
  ; r148PrintedPointInverseIsJplus = true
  ; printedAdjointIsAdjointExp = true
  ; oldDirectMinusJminusRouteTypeCompatible = true
  ; oldDirectMinusJminusRouteSourcePreferred = false
  ; correctedPrintedRoleRoutePreferred = true
  ; correctedRouteRequiresGlobalAdjointInverse = false
  ; selectedPhysicalRepresentationConstructed = false
  ; bishopToLegacyBridgeConstructed = false
  ; printedOperatorSemanticsConstructed = false
  ; cutThresholdConstructed = false
  ; physicalEq119Closed = false
  }

printedOuterIsDexpPlusIsTrue :
  r148PrintedOuterIsDexpPlus canonicalPrintedRoleCorrectionStatus ≡ true
printedOuterIsDexpPlusIsTrue = refl

printedPointInverseIsJplusIsTrue :
  r148PrintedPointInverseIsJplus canonicalPrintedRoleCorrectionStatus ≡ true
printedPointInverseIsJplusIsTrue = refl

oldDirectRouteSourcePreferredIsFalse :
  oldDirectMinusJminusRouteSourcePreferred canonicalPrintedRoleCorrectionStatus ≡ false
oldDirectRouteSourcePreferredIsFalse = refl

correctedPrintedRoleRoutePreferredIsTrue :
  correctedPrintedRoleRoutePreferred canonicalPrintedRoleCorrectionStatus ≡ true
correctedPrintedRoleRoutePreferredIsTrue = refl

physicalEq119ClosedIsFalse :
  physicalEq119Closed canonicalPrintedRoleCorrectionStatus ≡ false
physicalEq119ClosedIsFalse = refl

cmp98Path13PrintedRoleCorrectionProvenanceLevel : ProofLevel
cmp98Path13PrintedRoleCorrectionProvenanceLevel = machineChecked
