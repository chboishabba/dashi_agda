module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact as Owner

boundary : Owner.AdKSIQuantityBridgeBoundary
boundary = Owner.canonicalAdKSIQuantityBridgeBoundary

angstromTyped : Owner.angstromLength ≡ Owner.angstromLength
angstromTyped = refl

nanosecondTyped : Owner.nanosecondTime ≡ Owner.nanosecondTime
nanosecondTyped = refl

barTyped : Owner.oneBarPressure ≡ Owner.oneBarPressure
barTyped = refl

kramersUnitTyped : Owner.kramersRateUnitSI ≡ Owner.kramersRateUnitSI
kramersUnitTyped = refl

molarEnergyConversionTyped : Owner.oneTenthKcalPerMolSI ≡ Owner.oneTenthKcalPerMolSI
molarEnergyConversionTyped = refl

siSourceRetained : Owner.siSourceDOI ≡ "10.59161/AUEZ1291"
siSourceRetained = refl
