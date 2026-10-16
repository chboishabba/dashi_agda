module DASHI.Physics.Closure.BothwellYe2022AntigravityMetricClockBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022ChronometricGeodesyBridgeExact as Chronometric
import DASHI.Physics.Closure.BothwellYe2022RedshiftComparisonExact as Comparison
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityConsumerScopedCalibrationExact as Consumer

------------------------------------------------------------------------
-- BOTHWELL/YE 2022 x ANTIGRAVITY METRIC-CLOCK CALIBRATION
--
-- The antigravity stack already distinguishes a claim-specific
-- metricClockDiscriminator from static-load, free-fall, test-mass, inertial
-- and momentum discriminators.  The Bothwell/Ye experiment is therefore
-- useful here as a standard-gravity clock/reference surface, not as positive
-- evidence for an engineered metric response.
--
-- This bridge deliberately pays only the reference coordinate:
--
--   * a source-bounded ordinary-gravity clock comparison exists;
--   * local gravity, SI c/metre and the reported clock coordinate are welded;
--   * the result can serve as a negative-control/reference surface for future
--     engineeredMetricResponse consumers.
--
-- It does NOT construct the claim-specific consumer adequacy witness required
-- by AntigravityConsumerScopedCalibrationExact and does not promote any exotic
-- gravity, negative-G, sign-reversal or mechanism claim.
------------------------------------------------------------------------

metricClockDiscriminator : Anti.RequiredDiscriminator
metricClockDiscriminator = Anti.metricClockDiscriminator

engineeredMetricResponse : Anti.AntigravityClaim
engineeredMetricResponse = Anti.engineeredMetricResponse

canonicalBothwellYe2022RedshiftComparison : Comparison.BothwellYe2022ComparisonReceipt
canonicalBothwellYe2022RedshiftComparison = Comparison.canonicalBothwellYe2022ComparisonReceipt

canonicalRequiredDiscriminatorForEngineeredMetricResponse :
  Anti.requiredDiscriminator engineeredMetricResponse ≡ metricClockDiscriminator
canonicalRequiredDiscriminatorForEngineeredMetricResponse = refl

record BothwellYe2022AntigravityMetricClockBridge : Set₁ where
  field
    chronometricReference : Chronometric.BothwellYe2022ChronometricGeodesyBridge
    chronometricReferenceIsCanonical :
      chronometricReference ≡ Chronometric.canonicalBothwellYe2022ChronometricGeodesyBridge

    publicComparison : Comparison.BothwellYe2022ComparisonReceipt
    publicComparisonIsCanonical :
      publicComparison ≡ Comparison.canonicalBothwellYe2022ComparisonReceipt

    consumerCalibrationBoundary : Consumer.ConsumerScopedCalibrationBoundary
    consumerCalibrationBoundaryIsCanonical :
      consumerCalibrationBoundary ≡ Consumer.canonicalConsumerScopedCalibrationBoundary

    targetClaim : Anti.AntigravityClaim
    targetClaimIsEngineeredMetricResponse :
      targetClaim ≡ Anti.engineeredMetricResponse

    requiredDiscriminator : Anti.RequiredDiscriminator
    requiredDiscriminatorIsMetricClock :
      requiredDiscriminator ≡ Anti.metricClockDiscriminator

    standardMetricClockReferenceConstructed : Bool
    standardMetricClockReferenceConstructedIsTrue :
      standardMetricClockReferenceConstructed ≡ true

    standardGRRedshiftComparisonAvailable : Bool
    standardGRRedshiftComparisonAvailableIsTrue :
      standardGRRedshiftComparisonAvailable ≡ true

    ordinaryGravityClockReferenceForExoticComparison : Bool
    ordinaryGravityClockReferenceForExoticComparisonIsTrue :
      ordinaryGravityClockReferenceForExoticComparison ≡ true

    sameObjectExoticInterventionEvidencePresent : Bool
    sameObjectExoticInterventionEvidencePresentIsFalse :
      sameObjectExoticInterventionEvidencePresent ≡ false

    antigravityMetricClockConsumerAdequacyConstructed : Bool
    antigravityMetricClockConsumerAdequacyConstructedIsFalse :
      antigravityMetricClockConsumerAdequacyConstructed ≡ false

    engineeredMetricResponseObserved : Bool
    engineeredMetricResponseObservedIsFalse :
      engineeredMetricResponseObserved ≡ false

    negativeGInferred : Bool
    negativeGInferredIsFalse : negativeGInferred ≡ false

    antigravityMechanismValidated : Bool
    antigravityMechanismValidatedIsFalse :
      antigravityMechanismValidated ≡ false

    antigravityPromotionAllowed : Bool
    antigravityPromotionAllowedIsFalse :
      antigravityPromotionAllowed ≡ false

    reading : List String

open BothwellYe2022AntigravityMetricClockBridge public

canonicalBothwellYe2022AntigravityMetricClockBridge :
  BothwellYe2022AntigravityMetricClockBridge
canonicalBothwellYe2022AntigravityMetricClockBridge = record
  { chronometricReference = Chronometric.canonicalBothwellYe2022ChronometricGeodesyBridge
  ; chronometricReferenceIsCanonical = refl
  ; publicComparison = Comparison.canonicalBothwellYe2022ComparisonReceipt
  ; publicComparisonIsCanonical = refl
  ; consumerCalibrationBoundary = Consumer.canonicalConsumerScopedCalibrationBoundary
  ; consumerCalibrationBoundaryIsCanonical = refl
  ; targetClaim = Anti.engineeredMetricResponse
  ; targetClaimIsEngineeredMetricResponse = refl
  ; requiredDiscriminator = Anti.metricClockDiscriminator
  ; requiredDiscriminatorIsMetricClock = refl
  ; standardMetricClockReferenceConstructed = true
  ; standardMetricClockReferenceConstructedIsTrue = refl
  ; standardGRRedshiftComparisonAvailable = true
  ; standardGRRedshiftComparisonAvailableIsTrue = refl
  ; ordinaryGravityClockReferenceForExoticComparison = true
  ; ordinaryGravityClockReferenceForExoticComparisonIsTrue = refl
  ; sameObjectExoticInterventionEvidencePresent = false
  ; sameObjectExoticInterventionEvidencePresentIsFalse = refl
  ; antigravityMetricClockConsumerAdequacyConstructed = false
  ; antigravityMetricClockConsumerAdequacyConstructedIsFalse = refl
  ; engineeredMetricResponseObserved = false
  ; engineeredMetricResponseObservedIsFalse = refl
  ; negativeGInferred = false
  ; negativeGInferredIsFalse = refl
  ; antigravityMechanismValidated = false
  ; antigravityMechanismValidatedIsFalse = refl
  ; antigravityPromotionAllowed = false
  ; antigravityPromotionAllowedIsFalse = refl
  ; reading =
      "The Bothwell/Ye clock supplies a standard-gravity metric/clock reference coordinate for the existing antigravity metricClockDiscriminator lane."
      ∷ "The public measured-versus-gh/c^2 comparison and chronometric-geodesy weld make this useful as an ordinary-gravity reference or negative-control surface for future engineered-metric claims."
      ∷ "It does not observe an engineered metric response, negative G, sign-reversed gravity, or an antigravity mechanism."
      ∷ "Claim-specific antigravity consumer adequacy and promotion therefore remain fail-closed."
      ∷ []
  }

canonicalStandardMetricClockReferenceExists :
  standardMetricClockReferenceConstructed
    canonicalBothwellYe2022AntigravityMetricClockBridge
  ≡ true
canonicalStandardMetricClockReferenceExists = refl

canonicalAntigravityPromotionStillClosed :
  antigravityPromotionAllowed
    canonicalBothwellYe2022AntigravityMetricClockBridge
  ≡ false
canonicalAntigravityPromotionStillClosed = refl
