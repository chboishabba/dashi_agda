module DASHI.Physics.QuantumSensors.NVSIMetrologyReadoutAdapterExact where

-- Physically dimensioned NV sensing/readout contract.
-- SOURCE: BIPM, SI Brochure, 9th ed (2019), revision 4.01 (2026),
-- DOI 10.59161/AUEZ1291. SI formal representation owner:
-- DASHI.Physics.Units.SI (pre-existing).
-- NV axial energy owner: diamond MCG PR #1238.
-- SAXON Q source/experiment ownership: PR #1270.
-- THIS ADAPTER is a DASHI formal extension (26 October 2026).
-- No measured values, inferred constants, or constructed unit conversion.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.Units.SI as SI using
  (Quantity; Measurement; Unit; unitScale; nanoScale;
   Frequency; MagneticFluxDensity; Time; Power;
   hertz; tesla; second; watt)
import DASHI.Physics.QuantumSensors.NVSpinOneAxialExact as Axial

-- Each input quantity has its own dimension, and measured data retain
-- an uncertainty and provenance receipt. A rational axial-model value
-- is not an SI quantity by implicit coercion.
record NVSIReadoutCalibration : Set where
  field
    magneticField : SI.Measurement SI.MagneticFluxDensity SI.nanoScale
    driveFrequency : SI.Measurement SI.Frequency SI.unitScale
    opticalPumpPower : SI.Measurement SI.Power SI.unitScale
    integrationTime : SI.Measurement SI.Time SI.unitScale
    magneticFieldUnit : SI.Unit SI.MagneticFluxDensity
    frequencyUnit : SI.Unit SI.Frequency
    powerUnit : SI.Unit SI.Power
    durationUnit : SI.Unit SI.Time
    instrumentSource : String
    instrumentVersion : String
open NVSIReadoutCalibration public

-- The calibrated physical SI quantities, qutrit Hamiltonian rational
-- coefficients and photon statistics need an explicit conversion/fit.
-- In particular a gyromagnetic coefficient expressed in Hz/T is not
-- the same as an angular-frequency coefficient in rad/(s T).
record ModelToSIReceipt : Set where
  field
    calibration : NVSIReadoutCalibration
    axialModel : Axial.AxialNV
    mappingSource : String
    mappingVersion : String
    rationalToSIForwardModel : Set
    forwardModelWitness : rationalToSIForwardModel
open ModelToSIReceipt public

-- These are exact same-dimension identities, not numerical unit laws.
magneticDimensionMatches :
  SI.MagneticFluxDensity ≡ SI.MagneticFluxDensity
magneticDimensionMatches = refl

frequencyDimensionMatches : SI.Frequency ≡ SI.Frequency
frequencyDimensionMatches = refl
