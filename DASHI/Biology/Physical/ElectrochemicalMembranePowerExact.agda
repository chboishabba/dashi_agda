module DASHI.Biology.Physical.ElectrochemicalMembranePowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- A. L. Hodgkin and A. F. Huxley,
-- "A quantitative description of membrane current and its application to
-- conduction and excitation in nerve", The Journal of Physiology 117 (1952),
-- 500-544. DOI: 10.1113/jphysiol.1952.sp004764.
--
-- Peter Mitchell,
-- "Coupling of Phosphorylation to Electron and Hydrogen Transfer by a
-- Chemi-Osmotic type of Mechanism", Nature 191 (1961), 144-148.
-- DOI: 10.1038/191144a0.
--
-- Michael Levin,
-- "Bioelectric signaling: Reprogrammable circuits underlying embryogenesis,
-- regeneration, and cancer", Cell 184 (2021), 1971-1989.
-- DOI: 10.1016/j.cell.2021.02.034.
--
-- DASHI CONTRIBUTION
--
-- Exact finite arithmetic for two physical bookkeeping identities used by the
-- developmental lane: an Ohmic gap-junction current magnitude g*ΔV, and a
-- metabolic power budget J_ATP*ΔG_ATP.  This is not a calibrated ion-channel
-- model; the SI carrier types and source-facing mechanism boundaries remain
-- explicit.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.SIBiologyDimensionsExact as BioSI
import DASHI.Physics.Units.SI as SI
import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric
import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as ChemistryWave

conductiveCurrentMagnitude : Nat → Nat → Nat
conductiveCurrentMagnitude conductance voltageDifference =
  conductance * voltageDifference

electricalPowerMagnitude : Nat → Nat → Nat
electricalPowerMagnitude conductance voltageDifference =
  conductiveCurrentMagnitude conductance voltageDifference * voltageDifference

metabolicPowerMagnitude : Nat → Nat → Nat
metabolicPowerMagnitude molarFlow molarFreeEnergy = molarFlow * molarFreeEnergy

canonicalGapConductance : Nat
canonicalGapConductance = 2

canonicalVoltageDifference : Nat
canonicalVoltageDifference = 2

canonicalElectricalPower :
  electricalPowerMagnitude canonicalGapConductance canonicalVoltageDifference ≡ 8
canonicalElectricalPower = refl

canonicalATPFlow : Nat
canonicalATPFlow = 3

canonicalATPFreeEnergy : Nat
canonicalATPFreeEnergy = 4

canonicalMetabolicPower :
  metabolicPowerMagnitude canonicalATPFlow canonicalATPFreeEnergy ≡ 12
canonicalMetabolicPower = refl

canonicalPumpFitsMetabolicBudget :
  electricalPowerMagnitude canonicalGapConductance canonicalVoltageDifference
    ≤ metabolicPowerMagnitude canonicalATPFlow canonicalATPFreeEnergy
canonicalPumpFitsMetabolicBudget =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

------------------------------------------------------------------------
-- SI-typed carrier signature.
------------------------------------------------------------------------

record MembranePowerSISignature : Set₁ where
  field
    membraneVoltage : Set
    junctionConductance : Set
    electricalCurrent : Set
    metabolicMolarFlow : Set
    molarFreeEnergy : Set
    physicalPower : Set

    voltageIsSI : membraneVoltage ≡ SI.Quantity SI.Voltage SI.milliScale
    conductanceIsSI : junctionConductance ≡ SI.Quantity SI.Conductance SI.nanoScale
    currentIsSI : electricalCurrent ≡ SI.Quantity SI.Current SI.nanoScale
    molarFlowIsSI : metabolicMolarFlow ≡ SI.Quantity BioSI.MolarFlowRate SI.nanoScale
    molarEnergyIsSI : molarFreeEnergy ≡ SI.Quantity SI.MolarEnergy SI.unitScale
    powerIsSI : physicalPower ≡ SI.Quantity SI.Power SI.nanoScale

open MembranePowerSISignature public

canonicalMembranePowerSISignature : MembranePowerSISignature
canonicalMembranePowerSISignature = record
  { membraneVoltage = SI.Quantity SI.Voltage SI.milliScale
  ; junctionConductance = SI.Quantity SI.Conductance SI.nanoScale
  ; electricalCurrent = SI.Quantity SI.Current SI.nanoScale
  ; metabolicMolarFlow = SI.Quantity BioSI.MolarFlowRate SI.nanoScale
  ; molarFreeEnergy = SI.Quantity SI.MolarEnergy SI.unitScale
  ; physicalPower = SI.Quantity SI.Power SI.nanoScale
  ; voltageIsSI = refl
  ; conductanceIsSI = refl
  ; currentIsSI = refl
  ; molarFlowIsSI = refl
  ; molarEnergyIsSI = refl
  ; powerIsSI = refl
  }

------------------------------------------------------------------------
-- The existing BioelectricNetwork and BioelectricChemistryWaveAdapter remain
-- the mechanism owners.  This module supplies dimensional and finite-budget
-- arithmetic rather than replacing those interfaces.
------------------------------------------------------------------------
