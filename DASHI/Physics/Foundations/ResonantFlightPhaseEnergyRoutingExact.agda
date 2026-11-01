module DASHI.Physics.Foundations.ResonantFlightPhaseEnergyRoutingExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Phase-resolved energy routing.
------------------------------------------------------------------------

data PowerRole : Set where
  drive regenerate store return dissipate : PowerRole

record PhasePowerSample : Set₁ where
  constructor phase-power-sample
  field
    Phase Torque Velocity Power : Set
    phase : Phase
    torque : Torque
    velocity : Velocity
    power : Power

open PhasePowerSample public

record PowerClassifier : Set₁ where
  constructor power-classifier
  field
    Power : Set
    classify : Power → PowerRole

open PowerClassifier public

record PhasePowerSchedule : Set₁ where
  constructor phase-power-schedule
  field
    Phase Power : Set
    sample : Phase → Power
    role : Phase → PowerRole

open PhasePowerSchedule public

record RegenerativePhaseRoute : Set₁ where
  constructor regenerative-phase-route
  field
    Phase WingState StoreState BusState : Set
    wingAt : Phase → WingState
    capture : WingState → StoreState
    storeToBus : StoreState → BusState
    returnFromBus : BusState → WingState

open RegenerativePhaseRoute public

record PhaseWindowRouting : Set₁ where
  constructor phase-window-routing
  field
    Phase : Set
    inDriveWindow : Phase → Bool
    inRegenerationWindow : Phase → Bool
    inStorageWindow : Phase → Bool
    inReturnWindow : Phase → Bool

open PhaseWindowRouting public

------------------------------------------------------------------------
-- A neutral periodic cycle may contain multiple power roles even when
-- the geometric trajectory is fixed.
------------------------------------------------------------------------

record NaturalCycleEnergyPolicy : Set₁ where
  constructor natural-cycle-energy-policy
  field
    Phase : Set
    policy : Phase → PowerRole

open NaturalCycleEnergyPolicy public
