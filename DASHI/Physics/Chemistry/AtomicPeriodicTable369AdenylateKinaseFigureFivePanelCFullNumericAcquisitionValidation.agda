module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelCFullNumericAcquisitionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelCFullNumericAcquisitionExact as Full

-- Regression root for the full-resolution same-object Figure-5 panel-c readout.
-- The production owner must expose all eight printed relative free energies,
-- all visible directed Kramers-rate labels, and the six forward route-edge
-- payments used by the existing weighted AdK graph.

stateEnergyCountIsEight : Full.stateEnergyCount ≡ 8
stateEnergyCountIsEight = refl

directedRateCountIsTwenty : Full.directedRateCount ≡ 20
directedRateCountIsTwenty = refl

allSixRouteForwardRatesPaid : Full.allSixRouteForwardRatesPaid ≡ true
allSixRouteForwardRatesPaid = refl

allEightStateEnergiesPaid : Full.allEightStateEnergiesPaid ≡ true
allEightStateEnergiesPaid = refl

kramersRatesRemainNonExperimental : Full.kramersRatesAreExperimental ≡ false
kramersRatesRemainNonExperimental = refl
