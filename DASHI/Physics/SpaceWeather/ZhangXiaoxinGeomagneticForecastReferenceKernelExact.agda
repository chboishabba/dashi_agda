module DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastReferenceKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastSourceReplayExact as Z

------------------------------------------------------------------------
-- SOURCE-COORDINATE REFERENCE KERNEL
--
-- Executable here means that DASHI can project the source-exposed finite
-- aggregate coordinates deterministically.  The unpublished whitening,
-- CEEMDAN/CWT parameterisation and precursor rule are not reconstructed.
------------------------------------------------------------------------

record ForecastAggregate : Set where
  constructor forecast-aggregate
  field
    totalEvents : Nat
    stormEvents : Nat
    nonStormEvents : Nat
    accuratelyPredictedStormEvents : Nat
    reportedRecall : String
    selectedIMFs : String
    sourceTimeScale : String

open ForecastAggregate public

aggregateProjection : Z.ZhangForecastSourceReplay → ForecastAggregate
aggregateProjection r = forecast-aggregate
  (Z.ZhangForecastSourceReplay.totalCMEEvents r)
  (Z.ZhangForecastSourceReplay.kpAtLeast5Events r)
  (Z.ZhangForecastSourceReplay.kpBelow5Events r)
  (Z.ZhangForecastSourceReplay.accuratelyPredictedEvents r)
  (Z.ZhangForecastSourceReplay.reportedRecall r)
  (Z.ZhangForecastSourceReplay.selectedIMFs r)
  (Z.ZhangForecastSourceReplay.sourceBackedTimeScale r)

zhangForecastAggregateKernel : ForecastAggregate
zhangForecastAggregateKernel = aggregateProjection Z.sourceExactZhangForecastReplay

record ZhangReferenceKernelBoundary : Set where
  constructor zhang-reference-kernel-boundary
  field
    sourceAggregateProjectionExecutable : Bool
    sourceAggregateProjectionExecutableIsTrue : sourceAggregateProjectionExecutable ≡ true
    exactForecastAlgorithmExecutable : Bool
    exactForecastAlgorithmExecutableIsFalse : exactForecastAlgorithmExecutable ≡ false
    operationalThresholdRecovered : Bool
    operationalThresholdRecoveredIsFalse : operationalThresholdRecovered ≡ false

canonicalZhangReferenceKernelBoundary : ZhangReferenceKernelBoundary
canonicalZhangReferenceKernelBoundary =
  zhang-reference-kernel-boundary true refl false refl false refl

nextExecutableLeaf : String
nextExecutableLeaf =
  "recover source whitening/CEEMDAN/CWT hyperparameters, precursor quantisation rule and event-level input/output data before claiming an executable source forecast"
