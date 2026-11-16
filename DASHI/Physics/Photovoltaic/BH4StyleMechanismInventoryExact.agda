{-# OPTIONS --safe #-}
module DASHI.Physics.Photovoltaic.BH4StyleMechanismInventoryExact where

-- Mechanism-first, evidence-typed photovoltaic research catalogue.
-- Source-written on 2026-11-16. NOT yet Agda-kernel checked.
-- Reuses the discipline of the existing BH4 finite reaction / transport owner.
-- All finite witnesses below are SYNTHETIC, not device measurements.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

data Mechanism : Set where
  photonAbsorption photoEmission opticalFilmSplitting : Mechanism
  c3DipoleSelection diamondNVTwoPhotonIonisation : Mechanism
  quantumDotStarkTuning quantumDotMultipleExciton : Mechanism
  photosystemExcitation extracellularElectronTransfer : Mechanism
  rfGasRefraction rfGasAbsorption rfGasScattering : Mechanism
  nonlinearCapacitorDrive photovoltaicCarrierCollection : Mechanism
  waterEvaporation waterCondensation vapourRecompression : Mechanism
  heatPumpUpgrade usefulHighTemperatureHeat : Mechanism

data EvidenceLevel : Set where
  proposedMechanism literatureMechanism syntheticModel : EvidenceLevel
  independentlyMeasuredSameDevice : EvidenceLevel

record MechanismSourceReceipt : Set where
  constructor mechanismSourceReceipt
  field
    mechanism : Mechanism
    label : String
    sourceLocator : String
    evidence : EvidenceLevel
    assumedInputs : List Mechanism
    producedOutputs : List Mechanism
    competingMechanisms : List Mechanism
    unresolvedPhysicalGate : String

-- A statement that an effect has been observed does NOT certify a
-- source-matched usable-work or photovoltaic efficiency measurement.

quantumDotStarkReceipt : MechanismSourceReceipt
quantumDotStarkReceipt =
  mechanismSourceReceipt quantumDotStarkTuning
    "THz Stark modulation of CdSe/CdS core-shell quantum-dot optical absorption"
    "Pein et al., Nano Lett. 2017, DOI 10.1021/acs.nanolett.7b01837"
    literatureMechanism
    (photonAbsorption ∷ nonlinearCapacitorDrive ∷ [])
    (quantumDotStarkTuning ∷ photoEmission ∷ [])
    (photovoltaicCarrierCollection ∷ quantumDotMultipleExciton ∷ [])
    "Same quantum-dot device: optical gap vs time, absorbed energy, THz work, charge extraction and output power"

diamondNVPhotoelectricReceipt : MechanismSourceReceipt
diamondNVPhotoelectricReceipt =
  mechanismSourceReceipt diamondNVTwoPhotonIonisation
    "NV- photoelectric spin readout through two optical excitations"
    "Bourgeois et al., Nature Communications 2015, DOI 10.1038/ncomms9577"
    literatureMechanism
    (photonAbsorption ∷ photonAbsorption ∷ [])
    (photovoltaicCarrierCollection ∷ [])
    (photoEmission ∷ [])
    "Distinguish bias-powered photoconductive gain from zero-bias photovoltaic electric work"

biophotovoltaicTransferReceipt : MechanismSourceReceipt
biophotovoltaicTransferReceipt =
  mechanismSourceReceipt extracellularElectronTransfer
    "Living cyanobacterial photosynthetic extracellular electron export"
    "Wang et al., Nature Communications 2026, DOI 10.1038/s41467-026-72407-7"
    literatureMechanism
    (photosystemExcitation ∷ [])
    (extracellularElectronTransfer ∷ photovoltaicCarrierCollection ∷ [])
    (photoEmission ∷ [])
    "Source-matched photon uptake, cellular maintenance, metabolism, electrode export and cell voltage"

rfAirRefractionReceipt : MechanismSourceReceipt
rfAirRefractionReceipt =
  mechanismSourceReceipt rfGasRefraction
    "Air index-gradient optical deflection; not identical to RF plasma opacity"
    "Schroedel et al., Nature Photonics 2024, DOI 10.1038/s41566-023-01304-y"
    literatureMechanism
    (rfGasRefraction ∷ [])
    (rfGasScattering ∷ [])
    (rfGasAbsorption ∷ [])
    "Measure modulation source, actual refractive index, phase, absorption and outgoing angular distribution"

-- Mechanism accounting, comparable to BH4 reaction/exchange state.
-- Do not collapse recovered or stored excitation into an electrical output.
record PhotonEnergyAllocation : Set where
  constructor photonEnergyAllocation
  field
    incomingSolar : Nat
    incomingRF : Nat
    initialStored : Nat
    exportedElectrical : Nat
    storedExcitationIncrease : Nat
    storedChemicalIncrease : Nat
    thermalResidual : Nat
    escapedOptical : Nat
    finalStored : Nat
    conservation :
      (incomingSolar + incomingRF) + initialStored
      ≡ exportedElectrical +
        (storedExcitationIncrease +
        (storedChemicalIncrease +
        (thermalResidual + (escapedOptical + finalStored))))

open PhotonEnergyAllocation public

-- Same input can have different physically useful output partitions.
-- These fixtures are energy QUANTA, not joules or watts.
electricDominant : PhotonEnergyAllocation
electricDominant = photonEnergyAllocation 100 0 0 40 10 0 50 0 0 refl

excitationDominant : PhotonEnergyAllocation
excitationDominant = photonEnergyAllocation 100 0 0 10 60 0 30 0 0 refl

sameSolarInput :
  incomingSolar electricDominant ≡ incomingSolar excitationDominant
sameSolarInput = refl

data Empty : Set where

differentElectricalExport :
  exportedElectrical electricDominant
  ≡ exportedElectrical excitationDominant → Empty
differentElectricalExport ()

-- Quantum-confined Stark modulation: a gap shift is a separate
-- state from a material-independent theorem about photovoltaic gain.
record QuantumDotStarkStep : Set where
  constructor quantumDotStarkStep
  field
    noDriveGapMilliEV : Nat
    drivenGapMilliEV : Nat
    downwardShiftMilliEV : Nat
    shiftAccounting : drivenGapMilliEV + downwardShiftMilliEV ≡ noDriveGapMilliEV

syntheticQuantumDotShift : QuantumDotStarkStep
syntheticQuantumDotShift = quantumDotStarkStep 2000 1500 500 refl

-- Excitation generation is not identical to export through a bioelectrode.
record BioElectronAllocation : Set where
  constructor bioElectronAllocation
  field
    photogenerated : Nat
    electrodeExported : Nat
    metabolismRetained : Nat
    recombined : Nat
    balance : photogenerated ≡ electrodeExported + (metabolismRetained + recombined)

syntheticBioAllocation : BioElectronAllocation
syntheticBioAllocation = bioElectronAllocation 100 3 90 7 refl

-- In a closed water inventory, evaporation and condensation have
-- distinct vapour and liquid compartments; both balances must agree.
record CoupledEvapCondenseHeatLoop : Set where
  constructor coupledEvapCondenseHeatLoop
  field
    initialVapour evaporated condensed finalVapour : Nat
    initialLiquid finalLiquid : Nat
    vapourBalance : initialVapour + evaporated ≡ finalVapour + condensed
    liquidBalance : initialLiquid + condensed ≡ finalLiquid + evaporated
    panelHeatAbsorbed compressorWork : Nat
    condenserHeat thermalLeak : Nat
    upgradeBalance : panelHeatAbsorbed + compressorWork ≡ condenserHeat + thermalLeak
    preheatRecovered highGradeHeatExported : Nat
    condenserPartition : condenserHeat ≡ preheatRecovered + highGradeHeatExported

open CoupledEvapCondenseHeatLoop public

syntheticClosedWaterAndHeat : CoupledEvapCondenseHeatLoop
syntheticClosedWaterAndHeat =
  coupledEvapCondenseHeatLoop
    5 10 10 5
    100 100 refl refl
    700 105
    780 25 refl
    280 500 refl

-- Named physical gaps: do not manufacture measurements from finite
-- type checking, energy equalities, or a DOI string.
data PhysicalResidual : Set where
  measuredRate measuredSpectralResponse measuredBiasEnergy : PhysicalResidual
  heatTransferCoefficient vapourPressureAndCOP : PhysicalResidual
  sameMaterialHamiltonian measuredContactResponse : PhysicalResidual
  temperatureResolvedStorage measuredHumidityAndAirExchange : PhysicalResidual
  measuredLifetime : PhysicalResidual
