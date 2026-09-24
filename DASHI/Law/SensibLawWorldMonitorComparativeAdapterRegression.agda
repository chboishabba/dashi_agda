module DASHI.Law.SensibLawWorldMonitorComparativeAdapterRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawWorldMonitorComparativeAdapterExact as W

boundary : W.WorldMonitorComparativeBoundary
boundary = W.canonicalWorldMonitorComparativeBoundary

forecastStillRepresentation :
  W.forecastRunTypedRepresentation boundary ≡ true
forecastStillRepresentation = refl

modelStillTheory :
  W.forecastModelTypedTheory boundary ≡ true
modelStillTheory = refl

dashboardStillConsumerProjection :
  W.dashboardTypedConsumerProjection boundary ≡ true
dashboardStillConsumerProjection = refl

forecastStillDoesNotAutoChangeWorld :
  W.forecastChangeAutomaticallyChangesWorld boundary ≡ false
forecastStillDoesNotAutoChangeWorld = refl

signalStillDoesNotCreateTruth :
  W.signalAppearanceCreatesClaimTruth boundary ≡ false
signalStillDoesNotCreateTruth = refl
