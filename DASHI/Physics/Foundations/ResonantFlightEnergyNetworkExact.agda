module DASHI.Physics.Foundations.ResonantFlightEnergyNetworkExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Separate human input, intermediate oscillator, inertial energy bus,
-- and wing resonators.  The formal layer records routing authority
-- without asserting a numerical efficiency not yet established.
------------------------------------------------------------------------

data EnergyStoreKind : Set where
  elastic pneumatic inertial aerodynamic human : EnergyStoreKind

record EnergyPort : Set₁ where
  constructor energy-port
  field
    EnergyState : Set
    state : EnergyState

open EnergyPort public

record RoutedEnergyNetwork : Set₁ where
  constructor routed-energy-network
  field
    Port : EnergyStoreKind → EnergyPort
    Transfer : EnergyStoreKind → EnergyStoreKind → Set

open RoutedEnergyNetwork public

record HumanOscillatorBusWingChain : Set₁ where
  constructor human-oscillator-bus-wing-chain
  field
    HumanInput HumanOscillator InertialBus WingOscillator : Set
    humanToOscillator : HumanInput → HumanOscillator
    oscillatorToBus : HumanOscillator → InertialBus
    busToWing : InertialBus → WingOscillator

open HumanOscillatorBusWingChain public

------------------------------------------------------------------------
-- Multiaxis spring box: controls may alter equilibrium, stiffness, and
-- coupling independently of the wing's instantaneous state.
------------------------------------------------------------------------

record MultiAxisSpringBox : Set₁ where
  constructor multiaxis-spring-box
  field
    Axis : Set
    SpringState : Set
    Control : Set
    equilibrium : Control → Axis → SpringState
    stiffness : Control → Axis → SpringState
    coupling : Control → Axis → Axis → SpringState

open MultiAxisSpringBox public

record TunableResonator : Set₁ where
  constructor tunable-resonator
  field
    State : Set
    Tuning : Set
    naturalMode : Tuning → State
    loadedMode : Tuning → State

open TunableResonator public

record WingResonatorBank : Set₁ where
  constructor wing-resonator-bank
  field
    Joint : Set
    Resonator : Joint → TunableResonator
    CruiseTuning : (j : Joint) → TunableResonator.Tuning (Resonator j)

open WingResonatorBank public

------------------------------------------------------------------------
-- Regenerative loading is represented as a route from a wing-load state
-- back to an energy store.  This deliberately distinguishes recovery
-- from dissipation.
------------------------------------------------------------------------

record RegenerativeWingLoading : Set₁ where
  constructor regenerative-wing-loading
  field
    WingLoad StoreState : Set
    recover : WingLoad → StoreState
    returnToWing : StoreState → WingLoad

open RegenerativeWingLoading public
