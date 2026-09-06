{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVSource.PlasmaEnergyPartitionExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Coarse energy-accounting carrier for a laser-produced tin-plasma event.
-- It deliberately separates useful in-band EUV from other channels.
-- Values are finite accounting coordinates, not a complete plasma model.

record PlasmaEnergyPartition : Set where
  constructor plasmaEnergyPartition
  field
    absorbedLaserEnergy : Nat
    inBandEUV          : Nat
    outOfBandRadiation : Nat
    kineticMaterial    : Nat
    thermalMaterial    : Nat
    unresolved         : Nat

open PlasmaEnergyPartition public

EnergyAccounted : PlasmaEnergyPartition → Set
EnergyAccounted x =
  absorbedLaserEnergy x ≡
  inBandEUV x + outOfBandRadiation x + kineticMaterial x +
  thermalMaterial x + unresolved x

-- Conversion efficiency represented exactly without division:
--   useful / absorbed = numerator / denominator.
record ConversionEfficiencyWitness (x : PlasmaEnergyPartition) : Set where
  constructor conversionEfficiencyWitness
  field
    numerator   : Nat
    denominator : Nat
    equation    : inBandEUV x * denominator ≡ absorbedLaserEnergy x * numerator

open ConversionEfficiencyWitness public

-- Synthetic exact fixture used only to make the accounting API executable.
-- 100 input units are partitioned into 5 useful in-band EUV units and other
-- channels.  The 5% number is NOT asserted as an ASML production efficiency.
examplePartition : PlasmaEnergyPartition
examplePartition = plasmaEnergyPartition 100 5 15 20 30 30

examplePartitionAccounted : EnergyAccounted examplePartition
examplePartitionAccounted = refl

exampleFivePercentWitness : ConversionEfficiencyWitness examplePartition
exampleFivePercentWitness = conversionEfficiencyWitness 5 100 refl

-- Public gross architecture only establishes a chain of transformations:
-- laser -> tin plasma -> EUV emission.  It does not collapse every non-useful
-- energy channel into a single 'loss' mechanism.
data EnergyChannel : Set where
  UsefulInBandPhoton : EnergyChannel
  OutOfBandPhoton    : EnergyChannel
  MaterialKinetic    : EnergyChannel
  MaterialThermal    : EnergyChannel
  UnresolvedChannel  : EnergyChannel
