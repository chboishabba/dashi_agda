module DASHI.Physics.QuantumVacuum.PhysicalQuantities where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

------------------------------------------------------------------------
-- A deliberately small, dimension-safe finite quantity layer.
--
-- Magnitudes are natural-number model values.  The wrappers prevent accidental
-- identification of energy, work, power, time, length, frequency, temperature,
-- area and spectral density while the analytic real-valued layer remains open.
------------------------------------------------------------------------

record Energy : Set where
  constructor energy
  field magnitude : Nat

record Work : Set where
  constructor work
  field magnitude : Nat

record Power : Set where
  constructor power
  field magnitude : Nat

record Time : Set where
  constructor time
  field magnitude : Nat

record Length : Set where
  constructor length
  field magnitude : Nat

record Area : Set where
  constructor area
  field magnitude : Nat

record Frequency : Set where
  constructor frequency
  field magnitude : Nat

record Temperature : Set where
  constructor temperature
  field magnitude : Nat

record SpectralDensity : Set where
  constructor spectralDensity
  field magnitude : Nat

record EnergyPerArea : Set where
  constructor energyPerArea
  field magnitude : Nat

record Pressure : Set where
  constructor pressure
  field magnitude : Nat

energyToWork : Energy → Work
energyToWork e = work (Energy.magnitude e)

workToEnergy : Work → Energy
workToEnergy w = energy (Work.magnitude w)

_+E_ : Energy → Energy → Energy
energy x +E energy y = energy (x + y)

_+W_ : Work → Work → Work
work x +W work y = work (x + y)

scaleEnergy : Nat → Energy → Energy
scaleEnergy n (energy x) = energy (n * x)

scaleWork : Nat → Work → Work
scaleWork n (work x) = work (n * x)

averagePower : Energy → Time → Power
averagePower (energy e) (time t) = power (e * t)

------------------------------------------------------------------------
-- `averagePower` is intentionally a finite accounting proxy rather than a
-- division operation: the analytic completion must provide a positive-time
-- denominator and prove the quotient law.  This receipt prevents the proxy
-- from being mistaken for the final dimensional theorem.
------------------------------------------------------------------------

record AnalyticPowerCompletion : Set₁ where
  constructor mkAnalyticPowerCompletion
  field
    Carrier : Set
    divideEnergyByTime : Energy → Time → Carrier
    positiveTimeRequired : Time → Set

energyWorkRoundTrip : (e : Energy) → workToEnergy (energyToWork e) ≡ e
energyWorkRoundTrip (energy e) = refl
