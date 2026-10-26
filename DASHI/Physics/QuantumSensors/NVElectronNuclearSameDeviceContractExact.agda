module DASHI.Physics.QuantumSensors.NVElectronNuclearSameDeviceContractExact where

-- Cross-PR consumer of actual MCG axial NV and optical-readout carriers.
-- Source owners: diamond MCG #1238; SAXON Q nuclear/Grover source audit #1270.
-- No newly postulated Hamiltonian or inferred spin-to-nucleus physical pulse.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Physics.QuantumSensors.NVSpinOneAxialExact as Axial
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon
import DASHI.Physics.QuantumSensors.NVReadoutRegisterBoundaryExact as Register

-- A *shared apparatus key* must accompany a model and each measurement.
-- No equality of device identities can be inferred from component types.
record SameDeviceExperiment (DeviceKey : Set) : Set₁ where
  field
    sourceDevice : DeviceKey
    controlDevice : DeviceKey
    opticalDevice : DeviceKey
    controlMatchesSource : controlDevice ≡ sourceDevice
    opticalMatchesSource : opticalDevice ≡ sourceDevice

    axialElectronModel : Axial.AxialNV
    electronReadout : C3.C3 → Photon.BinaryPhotonLikelihood

    -- A candidate nuclear-level -> electron-level basis readout map.
    -- It is deliberately an explicit field, NOT produced by axial energies.
    nuclearToElectron :
      Register.Level Register.nuclearMemory →
      Register.Level Register.electronSensor

    -- Typed source document / calibrated experimental receipts are additional
    -- consumer obligations and NOT supplied by the mathematical carrier.
    calibratedControl : Set
    calibratedControlReceipt : calibratedControl
    opticalResponseReceipt : Set
    opticalResponseWitness : opticalResponseReceipt
open SameDeviceExperiment public

-- The register distinction survives every physical readout hypothesis:
-- an electron-sensor label is not itself a nuclear logical value.
sensorLabel : C3.C3 → Register.Level Register.electronSensor
sensorLabel = Register.electronLevelChart

-- Equality of model-level device IDs is necessary bookkeeping but not a
-- proof that optical photons were recorded, hyperfine drive was applied,
-- or a quantum algorithm was implemented.
