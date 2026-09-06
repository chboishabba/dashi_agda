{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell

-- The existing Maxwell lane already treats source current and continuity as
-- distinct obligations.  Semiconductor drift-diffusion consumes the same
-- architectural separation while supplying its own constitutive current law.

record CarrierFluxState : Set where
  constructor carrierFluxState
  field
    carrierDensityCode : Nat
    electricFieldCode  : Nat
    mobilityCode       : Nat
    driftFluxCode      : Nat
    diffusionFluxCode  : Nat
    totalFluxCode      : Nat
    totalFluxAccounting : driftFluxCode + diffusionFluxCode ≡ totalFluxCode

open CarrierFluxState public

-- Division-free drift skeleton: J_drift scales with n * mu * E in the chosen
-- normalized units.  Charge sign/unit calibration remains a separate layer.
record DriftLawWitness : Set where
  constructor driftLawWitness
  field
    density  : Nat
    mobility : Nat
    field    : Nat
    drift    : Nat
    law      : density * mobility * field ≡ drift

open DriftLawWitness public

syntheticDrift : DriftLawWitness
syntheticDrift = driftLawWitness 2 3 5 30 refl

record CarrierContinuity : Set where
  constructor carrierContinuity
  field
    initialCarriers : Nat
    generated       : Nat
    incoming        : Nat
    finalCarriers   : Nat
    recombined      : Nat
    outgoing        : Nat
    conservation :
      initialCarriers + (generated + incoming) ≡
      finalCarriers + (recombined + outgoing)

open CarrierContinuity public

syntheticContinuity : CarrierContinuity
syntheticContinuity = carrierContinuity 100 20 10 95 15 20 refl

record MaxwellCurrentContinuityReuse : Set where
  constructor maxwellCurrentContinuityReuse
  field
    sourceAdapter : Maxwell.MaxwellExteriorCalculusAdapter
    currentCarrier : Maxwell.ThreeForm
    currentIsCanonical : currentCarrier ≡ Maxwell.sourceCurrentThreeForm

open MaxwellCurrentContinuityReuse public

canonicalMaxwellCurrentContinuityReuse : MaxwellCurrentContinuityReuse
canonicalMaxwellCurrentContinuityReuse =
  maxwellCurrentContinuityReuse
    Maxwell.canonicalMaxwellExteriorCalculusAdapter
    Maxwell.sourceCurrentThreeForm
    refl

-- Constitutive-law firewall: conservation alone does not determine current.
fluxA : CarrierFluxState
fluxA = carrierFluxState 10 4 2 80 20 100 refl

fluxB : CarrierFluxState
fluxB = carrierFluxState 10 4 1 40 20 60 refl

sameDensity : carrierDensityCode fluxA ≡ carrierDensityCode fluxB
sameDensity = refl

sameField : electricFieldCode fluxA ≡ electricFieldCode fluxB
sameField = refl

data ⊥ : Set where

sameDensityAndFieldDoNotDetermineFlux :
  totalFluxCode fluxA ≡ totalFluxCode fluxB → ⊥
sameDensityAndFieldDoNotDetermineFlux ()

data TransportResidual : Set where
  CarrierChargeCalibration : TransportResidual
  EinsteinRelation         : TransportResidual
  MobilityModel            : TransportResidual
  DiffusionCoefficient     : TransportResidual
  RecombinationGeneration  : TransportResidual
  BoundaryInjection        : TransportResidual
  DegenerateStatistics     : TransportResidual
  QuantumTransport         : TransportResidual
