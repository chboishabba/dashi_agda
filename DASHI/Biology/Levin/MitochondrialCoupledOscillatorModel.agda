module DASHI.Biology.Levin.MitochondrialCoupledOscillatorModel where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Abstract coupled-oscillator surface for ATP-synthase rows and adjacent
-- cristae.  This module states what a synchronization model must provide;
-- it does not assert that electromagnetic or mechanical coupling has been
-- experimentally established at the required strength.

record Oscillator : Set where
  field
    phaseCarrier : Set
    frequencyCarrier : Set
    phase : phaseCarrier
    frequency : frequencyCarrier

record CouplingWitness : Set where
  field
    nearestNeighbourCoupling : Bool
    crossFaceCoupling : Bool
    interCristaCoupling : Bool
    phaseErrorObservable : Bool
    synchronizationObserved : Bool

record CoupledCristaModel : Set where
  field
    oscillator : Oscillator
    coupling : CouplingWitness

    electromagneticMechanismMeasured : Bool
    vibrationalMechanismMeasured : Bool
    synchronizationGainMeasured : Bool

    couplingMechanismOpen : Bool
    couplingMechanismOpenIsTrue : couplingMechanismOpen ≡ true

    proximityDoesNotProveInductance : Bool
    proximityDoesNotProveInductanceIsFalse : proximityDoesNotProveInductance ≡ false

    phaseLockNotPromoted : Bool
    phaseLockNotPromotedIsFalse : phaseLockNotPromoted ≡ false

    reading : String

open CoupledCristaModel public

canonicalCoupledCristaModel : CoupledCristaModel
canonicalCoupledCristaModel = record
  { oscillator = record
      { phaseCarrier = Bool
      ; frequencyCarrier = Bool
      ; phase = false
      ; frequency = false
      }
  ; coupling = record
      { nearestNeighbourCoupling = true
      ; crossFaceCoupling = true
      ; interCristaCoupling = true
      ; phaseErrorObservable = false
      ; synchronizationObserved = false
      }
  ; electromagneticMechanismMeasured = false
  ; vibrationalMechanismMeasured = false
  ; synchronizationGainMeasured = false
  ; couplingMechanismOpen = true
  ; couplingMechanismOpenIsTrue = refl
  ; proximityDoesNotProveInductance = false
  ; proximityDoesNotProveInductanceIsFalse = refl
  ; phaseLockNotPromoted = false
  ; phaseLockNotPromotedIsFalse = refl
  ; reading = "A coupled-oscillator model requires measured phase, frequency, coupling gain, and perturbation response; adjacency and rotor motion alone do not establish synchronization"
  }
