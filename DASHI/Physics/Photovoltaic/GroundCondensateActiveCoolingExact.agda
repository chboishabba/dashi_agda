module DASHI.Physics.Photovoltaic.GroundCondensateActiveCoolingExact where

-- 2026-11-16: condensate RETURNS TO THE COLD-SIDE EVAPORATOR.
-- Distinguish heat sourced from solar PV, heat supplied from the
-- ground, heat rejected to ground, and exported high-grade heat.
-- These symbolic quantities have no source-claimed SI calibration.
-- No actual water steam-table/pressure law or PV coefficient is supplied.
-- Agda kernel status: NOT CHECKED.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

data GroundOperatingMode : Set where
  groundAsHeatSink groundAsHeatSource groundDisconnected : GroundOperatingMode

record VaporCompressionCycle : Set where
  constructor vaporCompressionCycle
  field
    -- h1: evaporator vapour out, h2: compressor vapour out,
    -- h3: condenser liquid out, h4: post-expansion mixture in.
    -- The same unit/mass basis is assumed across all h/Q/W terms.
    h1 h2 h3 h4 : Nat
    coldEvaporationHeat compressorWork condenserHeat : Nat

    returnExpansionIsenthalpic : h4 ≡ h3
    evaporatorEnthalpyIncrease : h1 ≡ h4 + coldEvaporationHeat
    compressorEnthalpyIncrease : h2 ≡ h1 + compressorWork
    condenserEnthalpyDecrease : h2 ≡ h3 + condenserHeat

    -- Physics first-law compatibility must be established for the
    -- selected same-cycle states and actual unit/calibration data.
    cycleFirstLaw :
      condenserHeat ≡ coldEvaporationHeat + compressorWork

open VaporCompressionCycle public

condenserHeatIncludesCompressorWork :
  (cycle : VaporCompressionCycle) ->
  Bound._≤_ (coldEvaporationHeat cycle) (condenserHeat cycle)
condenserHeatIncludesCompressorWork cycle =
  Bound.transportUpper
    (Bound.sym (cycleFirstLaw cycle))
    (Bound.≤-append (coldEvaporationHeat cycle) (compressorWork cycle))

record SolarGroundCoolingNetwork : Set where
  constructor solarGroundCoolingNetwork
  field
    mode : GroundOperatingMode
    incomingSolar : Nat
    pvElectricExport solarThermalLoad otherSolarOpticalExit : Nat
    solarBalance :
      incomingSolar ≡ pvElectricExport + (solarThermalLoad + otherSolarOpticalExit)

    groundSourceHeat groundSinkHeat : Nat
    groundSourcePumpWork groundSinkPumpWork : Nat

    selectedWaterCycle : VaporCompressionCycle
    -- PV and ground-source heat can enter the evaporator through
    -- distinct, measured heat exchangers.
    coldSideHeatBalance :
      coldEvaporationHeat selectedWaterCycle ≡ solarThermalLoad + groundSourceHeat

    condenserToPreheat condenserToUsefulHeat condenserLoss : Nat
    condenserOutputPartition :
      condenserHeat selectedWaterCycle ≡
      condenserToPreheat + (condenserToUsefulHeat + condenserLoss)

    -- Ground-sink heat rejection is separately measured: it is not
    -- the same energy object as solar input or useful exported heat.
    groundSinkNetworkAuthority : groundSinkHeat ≡ groundSinkHeat

open SolarGroundCoolingNetwork public

-- An illustrative source-independent enthalpy ledger:
-- h3=h4=100; h1=800; h2=906; Qcold=700; Wcomp=106; Qhot=806.
-- The work is rounded energy quanta, NOT a certified COP.
toyCompressionLedger : VaporCompressionCycle
toyCompressionLedger =
  vaporCompressionCycle
    800 906 100 100
    700 106 806
    refl refl refl refl refl

toyGroundAssistedCoolSolar : SolarGroundCoolingNetwork
toyGroundAssistedCoolSolar =
  solarGroundCoolingNetwork
    groundDisconnected
    1000 300 700 0 refl
    0 0 0 0
    toyCompressionLedger refl
    300 506 0 refl
    refl

-- No physical conclusion about a real compressor or groundwater loop
-- follows from the synthetic existence witness.
