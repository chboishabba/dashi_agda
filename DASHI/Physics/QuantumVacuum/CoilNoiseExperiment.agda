module DASHI.Physics.QuantumVacuum.CoilNoiseExperiment where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.DiscriminatingExperiment as D
import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- The experimentally useful coil conjecture is a spectral comparison.
-- Observation of an excess spectrum remains weaker than harvestable power.
------------------------------------------------------------------------

record CoilGeometry : Set where
  constructor mkCoilGeometry
  field
    turns      : Nat
    radius     : Q.Length
    temperature : Q.Temperature

record CoilNoiseSpectrum : Set where
  constructor mkCoilNoiseSpectrum
  field
    frequency : Q.Frequency
    measured  : Q.SpectralDensity
    thermalPrediction : Q.SpectralDensity
    radiationResistancePrediction : Q.SpectralDensity

record CoilNoiseSignal : Set where
  constructor mkCoilNoiseSignal
  field
    geometry : CoilGeometry
    spectrum : CoilNoiseSpectrum

-- Ordinary alternatives that must be controlled before assigning an excess
-- to a vacuum-fluctuation contribution.

data CoilNoiseNull : Set where
  johnsonNyquistNoise : CoilNoiseNull
  amplifierNoise      : CoilNoiseNull
  externalPickup      : CoilNoiseNull
  parasiticCapacitance : CoilNoiseNull
  ordinaryAntennaCoupling : CoilNoiseNull
  temperatureCalibration : CoilNoiseNull

CoilDiscrimination : Set₁
CoilDiscrimination =
  D.DiscriminatingExperiment CoilNoiseSignal CoilNoiseNull

record HarvestableCoilPower : Set where
  constructor mkHarvestableCoilPower
  field
    deliveredPower : Q.Power
    rectificationObserved : Set
    loadCouplingObserved  : Set
    detailedBalanceExcluded : Set

noiseObservationClaim : Surface.ExtractionClaim
noiseObservationClaim =
  Surface.mkExtractionClaim
    Surface.coilVacuumNoise
    Surface.transient
    Surface.preliminaryExperiment
    true true false false false

noiseSpectrumObservedDoesNotPromotePower :
  (d : CoilDiscrimination) →
  Surface.promotable? noiseObservationClaim ≡ false
noiseSpectrumObservedDoesNotPromotePower d = refl

record ReplicatedHarvestingClosure : Set₁ where
  constructor mkReplicatedHarvestingClosure
  field
    discrimination :
      D.ReplicatedDiscrimination CoilNoiseSignal CoilNoiseNull
    harvesting : HarvestableCoilPower
    resetAndReservoirAccounting : Set
