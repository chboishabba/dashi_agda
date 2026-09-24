module DASHI.Law.SensibLawComparativeCrossDomainBatteryRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawComparativeCrossDomainBatteryExact as B

boundary : B.ComparativeCrossDomainBattery
boundary = B.canonicalComparativeCrossDomainBattery

worldTheorySeparationStillHolds :
  B.worldChangesTheoryDoesNot boundary ≡ true
worldTheorySeparationStillHolds = refl

theoryWorldSeparationStillHolds :
  B.theoryChangesWorldDoesNot boundary ≡ true
theoryWorldSeparationStillHolds = refl

forecastStillDoesNotAutoChangeWorld :
  B.forecastAutomaticallyChangesWorld boundary ≡ false
forecastStillDoesNotAutoChangeWorld = refl

worldMonitorModelStillTypedTheory :
  B.worldMonitorModelTypedTheory boundary ≡ true
worldMonitorModelStillTypedTheory = refl

worldMonitorDashboardStillConsumerProjection :
  B.worldMonitorDashboardTypedConsumerProjection boundary ≡ true
worldMonitorDashboardStillConsumerProjection = refl

quotientStillQueryRelative :
  B.quotientMayBeQueryAdequateWithoutRawIdentity boundary ≡ true
quotientStillQueryRelative = refl

sameWorldTradePolicyDifferenceStillPossible :
  B.sameWorldDifferentTradePolicyPossible boundary ≡ true
sameWorldTradePolicyDifferenceStillPossible = refl

beliefStillSeparateFromWorld :
  B.beliefDeltaIsNotWorldDelta boundary ≡ true
beliefStillSeparateFromWorld = refl

tradeJustificationStillNotCausalProof :
  B.tradeJustificationCreatesCausalProof boundary ≡ false
tradeJustificationStillNotCausalProof = refl

comparisonStillCreatesNoTruth :
  B.comparisonCreatesTruth boundary ≡ false
comparisonStillCreatesNoTruth = refl
