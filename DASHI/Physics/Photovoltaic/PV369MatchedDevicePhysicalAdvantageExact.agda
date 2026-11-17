module DASHI.Physics.Photovoltaic.PV369MatchedDevicePhysicalAdvantageExact where

-- P1/P2/P7 same-source 369-specific physical advantage discriminator.
-- A nontrivial triadic/C3v device is compared against conventional same-
-- material and same-input engineering, NOT merely unitary orbital labels.
--
-- Exact math: if both observable net electrical outputs are equal because
-- the only change is transported coordinates, strict improvement is absurd.
-- The actual experimental advantage remains an UNINHABITED physical gate.
-- Agda Golden native kernel acceptance OPEN.

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.PV369NetHalfThresholdExact as Net
import DASHI.Physics.Photovoltaic.Atomic369BasisTransportNoFreeGainExact as Coord
import DASHI.Physics.Photovoltaic.GaAs111OpticalDeviceSourceWeldExact as Experiment

record MatchedMaterial369PhysicalAdvantage : Set where
  field
    conventional : Net.NetSolarElectricPVAcceptance
    proposed369 : Net.NetSolarElectricPVAcceptance

    sameSolarApertureAndEnergyGrid :
      Net.NetSolarElectricPVAcceptance.measuredIncidentApertureSolar conventional
      ≡ Net.NetSolarElectricPVAcceptance.measuredIncidentApertureSolar proposed369

    identicalSourceSpectrumTemperatureAndTime : String
    sourceMaterialCompositionAndDeviceGeometry : String
    sourceResolvedStrainQuantumHamiltonian : String
    independentlyMeasuredOpticalGain : String
    independentlyMeasuredCarrierExtraction : String
    measuredRFAndThermalAuxCost : String
    physical369OperatorNotJustBasisChange : String
    matchedConventionalNo369Control : String
    independentExperimentalReplication : String

    -- An actual measured strict net gain, after source/auxiliary/driver
    -- accounting, not a spectral-simulation surrogate or a C3 relabeling.
    strictlyGreaterNetElectricity :
      Bound._≤_
        (suc (Net.NetSolarElectricPVAcceptance.measuredNetElectricExport conventional))
        (Net.NetSolarElectricPVAcceptance.measuredNetElectricExport proposed369)

-- This no-go is independent of material-specific constants. If the
-- new '369 cell' is merely a change of basis, same physical observable
-- gives equality; equality and strict gain cannot both be true.
coordinateOnlyCannotCreateStrictElectricalAdvantage :
  (control candidate : Net.NetSolarElectricPVAcceptance) ->
  Net.NetSolarElectricPVAcceptance.measuredNetElectricExport control
    ≡ Net.NetSolarElectricPVAcceptance.measuredNetElectricExport candidate ->
  Bound._≤_
    (suc (Net.NetSolarElectricPVAcceptance.measuredNetElectricExport control))
    (Net.NetSolarElectricPVAcceptance.measuredNetElectricExport candidate) ->
  Net.False
coordinateOnlyCannotCreateStrictElectricalAdvantage
  control candidate refl proof =
    Net.successorNotLeItself
      (Net.NetSolarElectricPVAcceptance.measuredNetElectricExport control)
      proof

-- A single physical 369 advantage does NOT prove a >50% device.
-- A >50% device does NOT prove it uses 369 rather than ordinary C3v.
-- Full acceptance requires BOTH MatchedMaterial369PhysicalAdvantage
-- and Net.NetSolarElectricPVAcceptance on one source-matched sample.
record Verified369SolarBreakthrough : Set where
  field
    physicalDistinctAdvantage : MatchedMaterial369PhysicalAdvantage
    actualMeasured369Device :
      Net.NetSolarElectricPVAcceptance
    sameCandidateDevice :
      actualMeasured369Device
      ≡ MatchedMaterial369PhysicalAdvantage.proposed369 physicalDistinctAdvantage

-- Neither record is inhabited in this branch; no experimental gain claimed.
