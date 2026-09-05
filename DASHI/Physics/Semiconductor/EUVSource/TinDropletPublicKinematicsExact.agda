{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVSource.TinDropletPublicKinematicsExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Public ASML technology coordinates for one documented EUV-source regime.
-- These fixtures encode only quantities ASML publicly states: approximately
-- 25 micrometre tin droplets, approximately 70 m/s velocity, and a 50 kHz
-- droplet stream.  They do not encode nozzle geometry, pressure waveform,
-- temperature control, targeting tolerances, feedback gains, pulse timing,
-- plasma optimization, or any other non-public production recipe.

dropletDiameterMicrometre : Nat
dropletDiameterMicrometre = 25

dropletSpeedMetrePerSecond : Nat
dropletSpeedMetrePerSecond = 70

dropletRatePerSecond : Nat
dropletRatePerSecond = 50000

prePulseCountPerDroplet : Nat
prePulseCountPerDroplet = 1

mainPulseCountPerDroplet : Nat
mainPulseCountPerDroplet = 1

laserPulseCountPerDroplet : Nat
laserPulseCountPerDroplet = prePulseCountPerDroplet + mainPulseCountPerDroplet

laserPulseCountPerDropletExact : laserPulseCountPerDroplet ≡ 2
laserPulseCountPerDropletExact = refl

-- If one idealizes the publicly stated 70 m/s and 50 kHz stream as a uniform
-- train, successive droplet centres are separated by 1.4 mm = 1400 micrometre:
--
--   spacing * rate = speed * 10^6.
--
-- This is a derived ideal-spacing coordinate, not an assertion of actual
-- instantaneous spacing tolerance or jitter in a production source.

idealCentreSpacingMicrometre : Nat
idealCentreSpacingMicrometre = 1400

idealSpacingWitness :
  idealCentreSpacingMicrometre * dropletRatePerSecond ≡
  dropletSpeedMetrePerSecond * 1000000
idealSpacingWitness = refl

-- Two laser pulses per droplet at 50 kHz gives 100 kHz pulse-events in the
-- simple two-pulse accounting model.  This is an event-count identity only;
-- it says nothing about pulse energies, shapes, delays or optical efficiency.

idealLaserPulseEventsPerSecond : Nat
idealLaserPulseEventsPerSecond = laserPulseCountPerDroplet * dropletRatePerSecond

idealLaserPulseEventsPerSecondExact : idealLaserPulseEventsPerSecond ≡ 100000
idealLaserPulseEventsPerSecondExact = refl
