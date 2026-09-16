module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureSixPanelCFullNumericAcquisitionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureSixPanelCFullNumericAcquisitionExact as Full

stateEnergyCountIsEight : Full.stateEnergyCount ≡ 8
stateEnergyCountIsEight = refl

directedRateCountIsSixteen : Full.directedRateCount ≡ 16
directedRateCountIsSixteen = refl

allEightStateEnergiesPaid : Full.allEightStateEnergiesPaid ≡ true
allEightStateEnergiesPaid = refl

allDirectedRateLabelsPaid : Full.allDirectedRateLabelsPaid ≡ true
allDirectedRateLabelsPaid = refl

kramersRatesRemainNonExperimental : Full.kramersRatesAreExperimental ≡ false
kramersRatesRemainNonExperimental = refl
