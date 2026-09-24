module DASHI.Physics.Foundations.ResonantFlightMechanicalImpedanceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Complex-like mechanical impedance surface.
-- We keep resistance-like and reactance-like coordinates separate so
-- later numeric realizations can use complex numbers without requiring
-- them at this structural layer.
------------------------------------------------------------------------

record MechanicalImpedance : Set₁ where
  constructor mechanical-impedance
  field
    Resistive Reactive : Set
    resistance : Resistive
    reactance : Reactive

open MechanicalImpedance public

record MechanicalPort : Set₁ where
  constructor mechanical-port
  field
    Effort Flow : Set
    effort : Effort
    flow : Flow

open MechanicalPort public

record ImpedanceMatch : Set₁ where
  constructor impedance-match
  field
    Source Load MatchWitness : Set
    source : Source
    load : Load
    matched : Source → Load → MatchWitness

open ImpedanceMatch public

------------------------------------------------------------------------
-- Matrix-style coupling surface for flap/pitch/fold/twist resonators.
------------------------------------------------------------------------

record CoupledMechanicalImpedance : Set₁ where
  constructor coupled-mechanical-impedance
  field
    Axis : Set
    Entry : Axis → Axis → Set
    impedance : (i j : Axis) → Entry i j

open CoupledMechanicalImpedance public

record VariableImpedanceGeometry : Set₁ where
  constructor variable-impedance-geometry
  field
    Control Frequency : Set
    Impedance : Set
    seenImpedance : Control → Frequency → Impedance

open VariableImpedanceGeometry public

------------------------------------------------------------------------
-- Source → matching network → bus → wing → aerodynamic load.
------------------------------------------------------------------------

record FlightImpedanceChain : Set₁ where
  constructor flight-impedance-chain
  field
    Human HumanMatcher Bus WingMatcher Wing AeroLoad : Set
    humanMatch : Human → HumanMatcher
    toBus : HumanMatcher → Bus
    wingMatch : Bus → WingMatcher
    toWing : WingMatcher → Wing
    toAir : Wing → AeroLoad

open FlightImpedanceChain public

record ReflectedAerodynamicLoad : Set₁ where
  constructor reflected-aerodynamic-load
  field
    AeroLoad WingPort BusPort : Set
    loadAtWing : AeroLoad → WingPort
    reflectToBus : WingPort → BusPort

open ReflectedAerodynamicLoad public
