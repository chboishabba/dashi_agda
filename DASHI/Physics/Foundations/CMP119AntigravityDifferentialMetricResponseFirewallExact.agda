{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityDifferentialMetricResponseFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

------------------------------------------------------------------------
-- DELTA NORMALIZATION != DELTA GRAVITATIONAL SOURCE
--
-- The physical lock-in source is the SAME-STATE DIFFERENCE OF RENORMALIZED
-- METRIC RESPONSES.  A shared affine normalization-to-gravity calibration
--
--   Lambda = a V + c
--
-- is sufficient for the common additive term c to cancel, leaving
--
--   Delta Lambda = a Delta V.
--
-- The scale a and the endpoint same-state metric-response receipts are physical
-- inputs; they are not inferred from Delta V alone.
------------------------------------------------------------------------

record DifferentialMetricResponseReceipt : Set₁ where
  field
    normalizationOff : ℚ
    normalizationOn : ℚ

    normalizationToGravityScale : ℚ
    commonAdditiveGravityRenormalization : ℚ

    physicalLambdaOff : ℚ
    physicalLambdaOn : ℚ

    offAffineCalibration :
      physicalLambdaOff
      ≡ normalizationToGravityScale * normalizationOff
        + commonAdditiveGravityRenormalization

    onAffineCalibration :
      physicalLambdaOn
      ≡ normalizationToGravityScale * normalizationOn
        + commonAdditiveGravityRenormalization

    OffMetricResponseSameStateReceipt : Set
    offMetricResponseSameStateReceipt : OffMetricResponseSameStateReceipt

    OnMetricResponseSameStateReceipt : Set
    onMetricResponseSameStateReceipt : OnMetricResponseSameStateReceipt

    CommonCosmologicalRenormalizationConditionReceipt : Set
    commonCosmologicalRenormalizationConditionReceipt :
      CommonCosmologicalRenormalizationConditionReceipt

open DifferentialMetricResponseReceipt public

physicalDeltaLambda : DifferentialMetricResponseReceipt → ℚ
physicalDeltaLambda receipt =
  physicalLambdaOn receipt - physicalLambdaOff receipt

normalizationDifferenceMatchesMetricResponseDifference :
  (receipt : DifferentialMetricResponseReceipt) →
  physicalDeltaLambda receipt
  ≡ normalizationToGravityScale receipt
    * (normalizationOn receipt - normalizationOff receipt)
normalizationDifferenceMatchesMetricResponseDifference receipt =
  trans
    (cong₂ _-_
      (onAffineCalibration receipt)
      (offAffineCalibration receipt))
    (solve-∀
      (normalizationToGravityScale receipt)
      (normalizationOn receipt)
      (normalizationOff receipt)
      (commonAdditiveGravityRenormalization receipt))

record DifferentialMetricResponseBoundary : Set where
  constructor differential-metric-response-boundary
  field
    normalizationDifferenceAloneDeterminesPhysicalDeltaLambda : Bool
    sharedAffineCalibrationSufficesForAdditiveCancellation : Bool
    normalizationCountertermCancellationStillUseful : Bool
    sameStateMetricResponseDifferenceRequired : Bool
    commonCosmologicalRenormalizationConditionRequired : Bool
    scalarKottlerResponseRequiresPhysicalDeltaLambda : Bool
    propagatingTTModeRequiresAdditionalDynamicalProducer : Bool

canonicalDifferentialMetricResponseBoundary : DifferentialMetricResponseBoundary
canonicalDifferentialMetricResponseBoundary =
  differential-metric-response-boundary
    false true true true true true true

normalizationDifferenceAloneDeterminesPhysicalDeltaLambda : Bool
normalizationDifferenceAloneDeterminesPhysicalDeltaLambda = false

normalizationCountertermCancellationStillUseful : Bool
normalizationCountertermCancellationStillUseful = true

sameStateMetricResponseDifferenceRequired : Bool
sameStateMetricResponseDifferenceRequired = true

commonCosmologicalRenormalizationConditionRequired : Bool
commonCosmologicalRenormalizationConditionRequired = true
