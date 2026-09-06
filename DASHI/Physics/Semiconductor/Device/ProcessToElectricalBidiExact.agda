{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.ProcessToElectricalBidiExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Semiconductor.Doping.ImplantDiffusionAnnealExact as Doping
import DASHI.Physics.Semiconductor.Interfaces.SiSiO2DanglingBondExact as Interface
import DASHI.Physics.Semiconductor.Device.ElectrostaticMaxwellCrossPollinationExact as Electrostatic
import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Transport

-- BIDI capstone: process-state producers feed device-state consumers, while
-- electrical discrepancies can route back to the process coordinates that
-- remain capable of changing the observable.  This is not an inverse solver;
-- it is an explicit dependency carrier.

record ProcessDeviceWeld : Set where
  constructor processDeviceWeld
  field
    anneal          : Doping.AnnealState
    interface       : Interface.InterfaceState
    electrostatics  : Electrostatic.ElectrostaticCell
    transport       : Transport.CarrierFluxState
    thresholdCode   : Nat
    mobilityCode    : Nat
    leakageCode     : Nat
    driveCurrentCode : Nat

open ProcessDeviceWeld public

syntheticDevice : ProcessDeviceWeld
syntheticDevice =
  processDeviceWeld
    Doping.annealA
    Interface.interfaceB
    (Electrostatic.electrostaticCell 40 60 20 10 90)
    (Transport.carrierFluxState 10 4 2 80 20 100 refl)
    55
    2
    8
    100

-- Reverse-routing coordinates: an electrical mismatch does not by itself say
-- which producer is wrong.  The type names the physically distinct suspects.
data ElectricalResidualRoute : Set where
  RouteActiveDopant       : ElectricalResidualRoute
  RouteInterfaceTraps     : ElectricalResidualRoute
  RouteFixedCharge        : ElectricalResidualRoute
  RouteElectrostatics     : ElectricalResidualRoute
  RouteMobility           : ElectricalResidualRoute
  RouteRecombination      : ElectricalResidualRoute
  RouteContactResistance  : ElectricalResidualRoute
  RouteGeometry           : ElectricalResidualRoute
  RouteQuantumConfinement : ElectricalResidualRoute

-- Same threshold code is not enough to identify the hidden process/device
-- state; reverse diagnosis must preserve the fibre of candidate causes.
record ElectricalObservation : Set where
  constructor electricalObservation
  field
    observedThreshold : Nat
    observedDriveCurrent : Nat
    observedLeakage : Nat

open ElectricalObservation public

observe : ProcessDeviceWeld → ElectricalObservation
observe x =
  electricalObservation
    (thresholdCode x)
    (driveCurrentCode x)
    (leakageCode x)

syntheticObservation : observe syntheticDevice ≡ electricalObservation 55 100 8
syntheticObservation = refl
