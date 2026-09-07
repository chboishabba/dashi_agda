{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119SplitPhysicalStandardProvenanceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SplitPhysicalStandardStatus : Set where
  constructor splitPhysicalStandardStatus
  field
    combinedHistoricalRepresentationCompatibilityClosed : Bool
    preferredRouteRequiresCombinedRepresentation : Bool
    physicalVariationalRadiusSeparate : Bool
    standardR171RepresentationSeparate : Bool
    selectedCutOperatorSameObjectWeldRequired : Bool
    scalarCutThresholdRequired : Bool
    physicalEq119Closed : Bool
open SplitPhysicalStandardStatus public

canonicalSplitPhysicalStandardStatus : SplitPhysicalStandardStatus
canonicalSplitPhysicalStandardStatus =
  splitPhysicalStandardStatus true false true true true true false

combinedCompatibilityClosedIsTrue :
  combinedHistoricalRepresentationCompatibilityClosed
    canonicalSplitPhysicalStandardStatus ≡ true
combinedCompatibilityClosedIsTrue = refl

combinedRepresentationNoLongerPrimitive :
  preferredRouteRequiresCombinedRepresentation
    canonicalSplitPhysicalStandardStatus ≡ false
combinedRepresentationNoLongerPrimitive = refl

standardRepresentationIsSeparate :
  standardR171RepresentationSeparate canonicalSplitPhysicalStandardStatus ≡ true
standardRepresentationIsSeparate = refl

physicalEq119StillOpen :
  physicalEq119Closed canonicalSplitPhysicalStandardStatus ≡ false
physicalEq119StillOpen = refl

cmp98Path13SplitPhysicalStandardProvenanceLevel : ProofLevel
cmp98Path13SplitPhysicalStandardProvenanceLevel = machineChecked
