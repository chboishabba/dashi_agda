{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityDeviceMetricObservableCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Physics.Foundations.PositiveGActiveStressWeakFieldMetricExact as Metric
import DASHI.Physics.ExoticGravity.WeightMetricApparentMassExact as Weight

freeFallPrediction : ℚ → ℚ
freeFallPrediction radius = Metric.interiorOutwardAcceleration radius

supportWeightPrediction : ℚ → ℚ → ℚ
supportWeightPrediction passiveMass outwardAcceleration =
  - (passiveMass * outwardAcceleration)

clockFractionalShiftPrediction : ℚ → ℚ → ℚ
clockFractionalShiftPrediction potentialDifference inverseCSquared =
  potentialDifference * inverseCSquared

opticalMetricPrediction : ℚ → ℚ → ℚ
opticalMetricPrediction metricAmplitude opticalGain =
  metricAmplitude * opticalGain

supportWeightLinearInMetricAcceleration :
  ∀ m a0 a1 →
  supportWeightPrediction m a1 - supportWeightPrediction m a0
  ≡ - (m * (a1 - a0))
supportWeightLinearInMetricAcceleration = solve-∀

clockPredictionLinearInPotential :
  ∀ phi0 phi1 invC2 →
  clockFractionalShiftPrediction phi1 invC2
    - clockFractionalShiftPrediction phi0 invC2
  ≡ (phi1 - phi0) * invC2
clockPredictionLinearInPotential = solve-∀

opticalPredictionLinearInMetricAmplitude :
  ∀ h0 h1 gain →
  opticalMetricPrediction h1 gain - opticalMetricPrediction h0 gain
  ≡ (h1 - h0) * gain
opticalPredictionLinearInMetricAmplitude = solve-∀

record FourChannelMetricProjection : Set where
  constructor four-channel-metric-projection
  field
    MetricState : Set
    metricState : MetricState

    WeightObservation FreeFallObservation ClockObservation OpticalObservation : Set

    weightFromMetric : MetricState → WeightObservation
    freeFallFromMetric : MetricState → FreeFallObservation
    clockFromMetric : MetricState → ClockObservation
    opticalFromMetric : MetricState → OpticalObservation

    sameMetricAcrossAllFourChannels : Bool
    sameMetricAcrossAllFourChannelsIsTrue :
      sameMetricAcrossAllFourChannels ≡ true

open FourChannelMetricProjection public

record DeviceMetricObservableBoundary : Set where
  constructor device-metric-observable-boundary
  field
    weightIsMetricProjectionNotMetricIdentity : Bool
    freeFallIsIndependentMetricProjection : Bool
    clockIsIndependentMetricProjection : Bool
    opticalIsIndependentMetricProjection : Bool
    sameMetricMustFeedAllFourChannels : Bool
    weightOnlyResidualSufficientForMetricClaim : Bool

canonicalDeviceMetricObservableBoundary : DeviceMetricObservableBoundary
canonicalDeviceMetricObservableBoundary =
  device-metric-observable-boundary true true true true true false

existingWeightBoundary : Weight.WeightMetricBoundary
existingWeightBoundary = Weight.canonicalWeightMetricBoundary
