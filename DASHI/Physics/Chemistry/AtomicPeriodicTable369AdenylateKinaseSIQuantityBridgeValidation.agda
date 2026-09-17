module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact as Bridge

boundary = Bridge.canonicalAdKSIQuantityBridgeBoundary

_ : Bridge.sourceDistancesInjectedIntoSILength boundary ≡ true
_ = refl

_ : Bridge.sourceTimesInjectedIntoSITime boundary ≡ true
_ = refl

_ : Bridge.sourcePressureInjectedIntoSIPressure boundary ≡ true
_ = refl

_ : Bridge.sourceTemperatureInjectedIntoSITemperature boundary ≡ true
_ = refl

_ : Bridge.relativeEnergyInjectedIntoSIMolarEnergy boundary ≡ true
_ = refl

_ : Bridge.kramersDisplayRateInjectedIntoSIFrequency boundary ≡ true
_ = refl

_ : Bridge.angularDiffusionUsesDimensionlessRadianSquared boundary ≡ true
_ = refl

_ : Bridge.degreeToRadianExactFixedPointBridgeClaimed boundary ≡ false
_ = refl

_ : Bridge.unitConversionCreatesScientificPayment boundary ≡ false
_ = refl
