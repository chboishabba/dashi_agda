module DASHI.Physics.Closure.NSPeriodicConcreteAdaptiveChart where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Deterministic finite chart-selection and hysteresis receipt.
------------------------------------------------------------------------

data TestSpectrum : Set where
  zeroSpectrum geometricSpectrum powerSpectrum plateauFour plateauEight :
    TestSpectrum

data ChartDecision : Set where
  zeroBranch : ChartDecision
  normalizedChart : Nat → ChartDecision
  diffuseBranch : ChartDecision

selectTestSpectrum : TestSpectrum → ChartDecision
selectTestSpectrum zeroSpectrum = zeroBranch
selectTestSpectrum geometricSpectrum = normalizedChart 0
selectTestSpectrum powerSpectrum = normalizedChart 0
selectTestSpectrum plateauFour = normalizedChart 4
selectTestSpectrum plateauEight = diffuseBranch

plateauEightIsDiffuse :
  selectTestSpectrum plateauEight ≡ diffuseBranch
plateauEightIsDiffuse = refl

hysteresisNumerator hysteresisDenominator : Nat
hysteresisNumerator = 1
hysteresisDenominator = 8

finiteTraceSwitchCount : Nat
finiteTraceSwitchCount = 1

finiteTraceSwitchCountRegression : finiteTraceSwitchCount ≡ 1
finiteTraceSwitchCountRegression = refl

fixedAbsolutePacketFloorRejected : Bool
fixedAbsolutePacketFloorRejected = true

finiteTraceSwitchingLocallyFinite : Bool
finiteTraceSwitchingLocallyFinite = true

diffuseSpectrumImpliesBKM : Bool
diffuseSpectrumImpliesBKM = false

universalAdaptiveChartCoverageProved : Bool
universalAdaptiveChartCoverageProved = false
