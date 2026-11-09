module DASHI.Chemistry.HydrogenElectricalInputIntegrationExact where

-- Attribution (2026-11-09):
-- SI unit definitions are owned by the BIPM, via existing
-- DASHI.Physics.Units.SI (DOI 10.59161/AUEZ1291).
-- Electrical energy E = P Δt and P = VI for an appropriately selected
-- DC measurement boundary are standard electrical engineering prior art.
-- User-directed, ChatGPT-drafted formal reconstruction. No instrument
-- record, H2 yield, engine saving or inventor claim is inferred here.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
import DASHI.Physics.Units.SI as SI

record DCWindow : Set where
  constructor dcWindow
  field
    voltageV : Nat
    currentA : Nat
    elapsedSeconds : Nat

open DCWindow public

-- Exact arithmetic of a rectangular/quasi-constant DC sample.
-- Accuracy for a physically varying waveform is an independent
-- sampling/integration obligation. For AC or mixed power flow, use
-- measured signed real power; never blindly substitute RMS V*RMS I.
dcWindowJoules : DCWindow → Nat
dcWindowJoules w =
  (voltageV w * currentA w) * elapsedSeconds w

finiteDCTraceJoules : List DCWindow → Nat
finiteDCTraceJoules [] = 0
finiteDCTraceJoules (w ∷ ws) =
  dcWindowJoules w + finiteDCTraceJoules ws

finiteDCTraceSI :
  List DCWindow → SI.Quantity SI.Energy SI.unitScale
finiteDCTraceSI ws = SI.posQ (finiteDCTraceJoules ws)

-- Exactly the same nominal 15 V bus can supply 1.5 kWh or 15 kWh
-- over one hour simply by changing current from 100 A to 1000 A.
-- A voltage rating alone is neither power nor integrated energy.
lowerCurrentFixture : DCWindow
lowerCurrentFixture = dcWindow 15 100 3600

higherCurrentFixture : DCWindow
higherCurrentFixture = dcWindow 15 1000 3600

sameVoltageFixture :
  voltageV lowerCurrentFixture ≡ voltageV higherCurrentFixture
sameVoltageFixture = refl

lowerEnergyFixture :
  dcWindowJoules lowerCurrentFixture ≡ 5400000
lowerEnergyFixture = refl

higherEnergyFixture :
  dcWindowJoules higherCurrentFixture ≡ 54000000
higherEnergyFixture = refl

voltageDoesNotDetermineEnergy :
  dcWindowJoules lowerCurrentFixture
  ≡ dcWindowJoules higherCurrentFixture → ⊥
voltageDoesNotDetermineEnergy ()

record ElectricalTraceReceipt : Set₁ where
  field
    trace : List DCWindow
    voltageCalibration : Set
    currentCalibration : Set
    waveformAndSampleHoldValidity : Set
    matchedMeasurementWindow : Set
    signedPowerAndBatterySOCAccounted : Set
    importedHeatAndChemicalInputsSeparatelyCounted : Set
    genuineElectricEnergyMeasurement : Set

-- The existence of a DCWindow or a trace does not inhabit these
-- metrological/physical provenance fields or validate a commercial device.
