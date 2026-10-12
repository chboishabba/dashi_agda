{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityDifferentialMetricResponseFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Rational.Base using (ℚ; _-_)

------------------------------------------------------------------------
-- DELTA NORMALIZATION != DELTA GRAVITATIONAL SOURCE
--
-- Common additive normalization/counterterm pieces may cancel in a source
-- difference.  That is useful, but it does not by itself identify the
-- difference with a gravitational Delta-Lambda.  The physical lock-in source
-- is the SAME-STATE DIFFERENCE OF RENORMALIZED METRIC RESPONSES.
------------------------------------------------------------------------

record DifferentialMetricResponseReceipt : Set₁ where
  field
    normalizationOff : ℚ
    normalizationOn : ℚ

    physicalLambdaOff : ℚ
    physicalLambdaOn : ℚ

    OffMetricResponseSameStateReceipt : Set
    offMetricResponseSameStateReceipt : OffMetricResponseSameStateReceipt

    OnMetricResponseSameStateReceipt : Set
    onMetricResponseSameStateReceipt : OnMetricResponseSameStateReceipt

    CommonCosmologicalRenormalizationConditionReceipt : Set
    commonCosmologicalRenormalizationConditionReceipt :
      CommonCosmologicalRenormalizationConditionReceipt

    normalizationDifferenceMatchesMetricResponseDifference :
      normalizationOn - normalizationOff
      ≡ physicalLambdaOn - physicalLambdaOff

open DifferentialMetricResponseReceipt public

physicalDeltaLambda : DifferentialMetricResponseReceipt → ℚ
physicalDeltaLambda receipt =
  physicalLambdaOn receipt - physicalLambdaOff receipt

record DifferentialMetricResponseBoundary : Set where
  constructor differential-metric-response-boundary
  field
    normalizationDifferenceAloneDeterminesPhysicalDeltaLambda : Bool
    normalizationCountertermCancellationStillUseful : Bool
    sameStateMetricResponseDifferenceRequired : Bool
    commonCosmologicalRenormalizationConditionRequired : Bool
    scalarKottlerResponseRequiresPhysicalDeltaLambda : Bool
    propagatingTTModeRequiresAdditionalDynamicalProducer : Bool

canonicalDifferentialMetricResponseBoundary : DifferentialMetricResponseBoundary
canonicalDifferentialMetricResponseBoundary =
  differential-metric-response-boundary
    false true true true true true

normalizationDifferenceAloneDeterminesPhysicalDeltaLambda : Bool
normalizationDifferenceAloneDeterminesPhysicalDeltaLambda = false

normalizationCountertermCancellationStillUseful : Bool
normalizationCountertermCancellationStillUseful = true

sameStateMetricResponseDifferenceRequired : Bool
sameStateMetricResponseDifferenceRequired = true

commonCosmologicalRenormalizationConditionRequired : Bool
commonCosmologicalRenormalizationConditionRequired = true
