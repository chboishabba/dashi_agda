module DASHI.Physics.YangMills.BalabanLargeFieldSuppression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
import DASHI.Physics.Closure.YMLargeFieldTemporalCutSeparationAuthority
  as W3
import DASHI.Physics.Closure.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  as Sprint77

Scalar : Set
Scalar = String

data LargeFieldSuppressionObligation : Set where
  positiveSuppressionRate : LargeFieldSuppressionObligation
  summableLargeFieldActivity : LargeFieldSuppressionObligation
  spatialOnlyEffectiveActionInput : LargeFieldSuppressionObligation

canonicalLargeFieldSuppressionObligations :
  List LargeFieldSuppressionObligation
canonicalLargeFieldSuppressionObligations =
  positiveSuppressionRate
  ∷ summableLargeFieldActivity
  ∷ spatialOnlyEffectiveActionInput
  ∷ []

record LargeFieldSuppressionBound : Set₁ where
  field
    w3Receipt : W3.YMLargeFieldTemporalCutSeparationAuthorityReceipt
    sprint77Receipt :
      Sprint77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt
    temporalCutSeparationClosed :
      W3.largeFieldPolymersDoNotCrossTransferCut w3Receipt ≡ true
    sourceFloorKStartPinned :
      Sprint77.sourceFloorKStart sprint77Receipt ≡ "9"
    scaleKSuppressionAvailable :
      Sprint77.largeFieldSuppressionAvailableAtScaleK sprint77Receipt ≡ true
    largeFieldThreshold : Scalar
    suppressionRate : Scalar
    suppressionPositive : Bool
    largeFieldActivitySummable : Bool
    effectiveActionPolymersSpatialOnly : Bool
    suppressionPositiveIsFalse : suppressionPositive ≡ false
    largeFieldActivitySummableIsFalse :
      largeFieldActivitySummable ≡ false
    effectiveActionPolymersSpatialOnlyIsFalse :
      effectiveActionPolymersSpatialOnly ≡ false
    targetInequality : String
    openObligations : List LargeFieldSuppressionObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalLargeFieldSuppressionObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

currentLargeFieldSuppressionBound : LargeFieldSuppressionBound
currentLargeFieldSuppressionBound = record
  { w3Receipt = W3.canonicalYMLargeFieldTemporalCutSeparationAuthorityReceipt
  ; sprint77Receipt =
      Sprint77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  ; temporalCutSeparationClosed =
      W3.largeFieldPolymersDoNotCrossTransferCutIsTrue
        W3.canonicalYMLargeFieldTemporalCutSeparationAuthorityReceipt
  ; sourceFloorKStartPinned =
      Sprint77.sourceFloorKStartIsNine
        Sprint77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  ; scaleKSuppressionAvailable =
      Sprint77.largeFieldSuppressionAvailableAtScaleKIsTrue
        Sprint77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  ; largeFieldThreshold = "k_start = 9"
  ; suppressionRate = "unproved"
  ; suppressionPositive = false
  ; largeFieldActivitySummable = false
  ; effectiveActionPolymersSpatialOnly = false
  ; suppressionPositiveIsFalse = refl
  ; largeFieldActivitySummableIsFalse = refl
  ; effectiveActionPolymersSpatialOnlyIsFalse = refl
  ; targetInequality =
      "large-field activity <= exp (-gamma * large-field scale)"
  ; openObligations = canonicalLargeFieldSuppressionObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
