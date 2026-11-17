module DASHI.Physics.Photovoltaic.PV369PassiveAbsorbedEnergyCeilingExact where

-- PV P5 first-law audit of a passive, independently loaded photovoltaic
-- junction, reusing the original exact MOTOR energy ledger constructors.
-- Wavelength photon counts / EQE are not an ENERGY conservation identity.
-- The physical premise is a SOURCE-MEASURED absorption-to-electricity
-- balance for the SAME junction/aperture/illumination/time and real gross MPP.
-- P3 externally driven photoresponses require a separate measured signed
-- driving-work input. They cannot be inserted into passive P5 acceptance.
-- P4 genuine multiple-charge collection does not add incident photon ENERGY.
-- Golden Agda kernel acceptance OPEN; does not create an experiment.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.PV369NetHalfThresholdExact as Net
import DASHI.Physics.Photovoltaic.PV369IntervalRobustAcceptanceExact as Interval
import DASHI.Physics.Photovoltaic.PV369FourJunctionOpticsToMeasuredIVExact as Optical

record OriginalPassiveJunctionEnergy : Set where
  field
    absorbedSolarEnergy : Nat
    grossTerminalElectricalMPP : Nat
    otherHeatAndOpticalLoss : Nat
    originalSourceSamePowerQuantum :
      absorbedSolarEnergy ≡ grossTerminalElectricalMPP + otherHeatAndOpticalLoss

-- This is a derived no-free-energy bound. The optical/source
-- measurement equality above is a paid physical assumption, not refl.
passiveTerminalMPPAtMostAbsorbed :
  (s : OriginalPassiveJunctionEnergy) ->
  Bound._≤_ (OriginalPassiveJunctionEnergy.grossTerminalElectricalMPP s)
    (OriginalPassiveJunctionEnergy.absorbedSolarEnergy s)
passiveTerminalMPPAtMostAbsorbed s =
  Bound.transportUpper
    (Bound.sym (OriginalPassiveJunctionEnergy.originalSourceSamePowerQuantum s))
    (Bound.≤-append
      (OriginalPassiveJunctionEnergy.grossTerminalElectricalMPP s)
      (OriginalPassiveJunctionEnergy.otherHeatAndOpticalLoss s))

-- Assuming strict GROSS electrical MPP exceeds the ABSORBED photovoltaic
-- energy is incompatible with the same passive ledger.
passiveOverAbsorptionContradiction :
  (s : OriginalPassiveJunctionEnergy) ->
  Bound._≤_
    (suc (OriginalPassiveJunctionEnergy.absorbedSolarEnergy s))
    (OriginalPassiveJunctionEnergy.grossTerminalElectricalMPP s) ->
  Net.False
passiveOverAbsorptionContradiction s claimedExcess =
  Net.successorNotLeItself
    (OriginalPassiveJunctionEnergy.absorbedSolarEnergy s)
    (Interval.leTrans
      claimedExcess
      (passiveTerminalMPPAtMostAbsorbed s))

-- This ledger is for ONE passive optical-to-electrical cell.
-- For a 4T stack, every separately contacted source group must be
-- allocated genuine incident absorbed-energy inputs without duplication.
-- A series-connected GaInP/GaAs tandem is ONE electrical output group,
-- although it is TWO optically distinct junctions, and requires its own
-- same-energy allocation. The source-specific NREL 3J/2-output owner
-- remains a separate bridge.
