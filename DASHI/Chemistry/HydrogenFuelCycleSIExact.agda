module DASHI.Chemistry.HydrogenFuelCycleSIExact where

-- Attribution: SI unit definitions belong to BIPM SI Brochure 9th edition
-- (DASHI.Physics.Units.SI, DOI 10.59161/AUEZ1291).
-- The typed SI carrier is an existing DASHI formalisation. This adapter is
-- user-directed and ChatGPT-drafted (2026-11-09).
-- No measured electricity, heat, hydrogen flow, or physical efficiency
-- is manufactured by creating a typed record.

open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import Data.Nat.Base using (_≤_)
import DASHI.Physics.Units.SI as SI
import DASHI.Chemistry.HydrogenElectrolyserEnergyExact as Electrolyser

-- kWh is an energy unit (not power). 1 kWh = 3,600,000 J exactly by
-- conventional hour/kilo definitions. The magnitudes use SI.unitScale.
kilowattHourToJoule : Nat → SI.Quantity SI.Energy SI.unitScale
kilowattHourToJoule n = SI.posQ (n * 3600000)

oneKilowattHourRegression :
  kilowattHourToJoule 1 ≡ SI.posQ 3600000
oneKilowattHourRegression = refl

-- A common source receipt for battery/grid input and hydrogen output.
-- Units and decimal scale are checked by the type; numeric consistency,
-- accurate instrument calibration, HHV and heat accounting remain supplied
-- obligations. Quantity subtraction is not silently performed on unsigned
-- fixed-point magnitudes.
record SIHydrogenProcessReceipt : Set where
  field
    inputElectricalEnergy : SI.Measurement SI.Energy SI.unitScale
    hydrogenChemicalEnergyHHV : SI.Measurement SI.Energy SI.unitScale
    rejectedEnergy : SI.Measurement SI.Energy SI.unitScale
    storageEnergyIncrease : SI.Measurement SI.Energy SI.unitScale

    allAreJoules :
      SI.Measurement.unit inputElectricalEnergy ≡ SI.joule
    hydrogenIsInJoules :
      SI.Measurement.unit hydrogenChemicalEnergyHHV ≡ SI.joule
    heatIsInJoules :
      SI.Measurement.unit rejectedEnergy ≡ SI.joule
    storageIsInJoules :
      SI.Measurement.unit storageEnergyIncrease ≡ SI.joule

    inputMagnitudeIsNonnegative :
      SI.Quantity.negative (SI.Measurement.value inputElectricalEnergy) ≡ false
    hydrogenMagnitudeIsNonnegative :
      SI.Quantity.negative (SI.Measurement.value hydrogenChemicalEnergyHHV) ≡ false
    heatMagnitudeIsNonnegative :
      SI.Quantity.negative (SI.Measurement.value rejectedEnergy) ≡ false
    storageMagnitudeIsNonnegative :
      SI.Quantity.negative (SI.Measurement.value storageEnergyIncrease) ≡ false

    balance :
      SI.Quantity.magnitude (SI.Measurement.value inputElectricalEnergy)
        ≡
      SI.Quantity.magnitude (SI.Measurement.value hydrogenChemicalEnergyHHV)
        +
      (SI.Quantity.magnitude (SI.Measurement.value rejectedEnergy)
        +
       SI.Quantity.magnitude (SI.Measurement.value storageEnergyIncrease))

    -- Metrological provenance, calibration and HHV are independent from
    -- dimensional validity; a bare citation cannot supply these proofs.
    heatingValueConvention : String
    instrumentCalibrationReceipt : Set
    sameRunInventoryReceipt : Set

open SIHydrogenProcessReceipt public

siToElectrolyserFirstLaw :
  SIHydrogenProcessReceipt → Electrolyser.ElectrolyserFirstLaw
siToElectrolyserFirstLaw s = record
  { electricalWork =
      SI.Quantity.magnitude (SI.Measurement.value (inputElectricalEnergy s))
  ; generatedHydrogenHHV =
      SI.Quantity.magnitude (SI.Measurement.value (hydrogenChemicalEnergyHHV s))
  ; heatAndOtherLosses =
      SI.Quantity.magnitude (SI.Measurement.value (rejectedEnergy s))
  ; storedEnergyIncrease =
      SI.Quantity.magnitude (SI.Measurement.value (storageEnergyIncrease s))
  ; balance = balance s
  }

siHydrogenEnergyBound :
  (s : SIHydrogenProcessReceipt) →
  Electrolyser.generatedHydrogenHHV (siToElectrolyserFirstLaw s)
  ≤ Electrolyser.electricalWork (siToElectrolyserFirstLaw s)
siHydrogenEnergyBound s =
  Electrolyser.hydrogenHHVWithinElectricity (siToElectrolyserFirstLaw s)
