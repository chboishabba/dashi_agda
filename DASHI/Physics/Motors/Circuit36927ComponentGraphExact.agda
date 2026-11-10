module DASHI.Physics.Motors.Circuit36927ComponentGraphExact where

------------------------------------------------------------------------
-- DASHI contribution: generic user-specified circuit component graph.
-- This file carries no borrowed STL, STEP, manufacturer netlist, or
-- assumed measurements. Parameters have explicitly documented units.
--
-- Existing consumers can instantiate values, pins, physical laws and
-- source evidence; a component declaration alone is not an empirical
-- observation or a circuit-simulation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Foundations.Base369TriadicPhaseTower as Tower
import Base369 as B

data ComponentKind : Set where
  resistor capacitor inductor : ComponentKind
  voltageSource currentSource : ComponentKind
  diode transistor reedSwitch : ComponentKind
  transformer permanentMagnet coil rotor : ComponentKind
  groundPoint connector meter : ComponentKind

-- A measured value is intentionally not manufactured from a product
-- advertisement. Units are selected by the kind-specific constructors.
data NominalValue : Set where
  milliohms : Nat → NominalValue
  picofarads : Nat → NominalValue
  nanohenries : Nat → NominalValue
  millivolts : Nat → NominalValue
  microamps : Nat → NominalValue
  dimensionless : Nat → NominalValue
  unavailable : NominalValue

-- Values are NOT silently interpreted across different dimensions.
data Dimension : Set where
  resistance capacitance inductance voltage current pureNumber unknown : Dimension

valueDimension : NominalValue → Dimension
valueDimension (milliohms _) = resistance
valueDimension (picofarads _) = capacitance
valueDimension (nanohenries _) = inductance
valueDimension (millivolts _) = voltage
valueDimension (microamps _) = current
valueDimension (dimensionless _) = pureNumber
valueDimension unavailable = unknown

record Part : Set where
  constructor part
  field
    identifier : Nat
    kind : ComponentKind
    label : String
    nominal : NominalValue
    pinCount : Nat

record Pin : Set where
  constructor pin
  field
    componentIdentifier : Nat
    pinNumber : Nat

data Endpoint : Set where
  atPin : Pin → Endpoint
  atNamedNode : Nat → Endpoint

record Wire : Set where
  constructor wire
  field
    from to : Endpoint

-- A netlist can contain active and passive parts, multi-pin parts and
-- named junctions. Pin existence, unique component IDs and directed
-- edge interpretation require a separate well-formedness witness.
record Circuit : Set where
  constructor circuit
  field
    parts : Nat → Part
    declaredPartCount : Nat
    connections : Nat → Wire
    declaredWireCount : Nat
    revision : String

-- Node identity is not physical position. Positions enter a separate
-- geometric correspondence where they can be measured or estimated.
record CircuitInterpretation (c : Circuit) : Set₁ where
  constructor interpretCircuit
  field
    WellFormed : Set
    sameRevisionEvidence : Set
    electricalLaws : Set

-- Plain directed graph reachability; it does not solve voltages or
-- convert a component into an ideal zero-impedance connection.
record WiringGraph : Set₁ where
  constructor wiringGraph
  field
    Edge : Endpoint → Endpoint → Set

data Route (g : WiringGraph) : Endpoint → Endpoint → Set where
  here : ∀ {x} → Route g x x
  step : ∀ {x y z} →
    WiringGraph.Edge g x y →
    Route g y z →
    Route g x z

composeRoute :
  (g : WiringGraph) {x y z : Endpoint} →
  Route g x y → Route g y z → Route g x z
composeRoute g here q = q
composeRoute g (step e p) q = step e (composeRoute g p q)

-- The 3/9/27 phase carrier is explicitly borrowed from the existing
-- Base369 triadic tower, not a newly invented numerical doctrine.
record PhaseTaggedPart : Set where
  constructor phaseTaggedPart
  field
    component : Part
    finePhase : Tower.Phase27

coarsePhase : PhaseTaggedPart → B.TriTruth
coarsePhase tagged =
  Tower.phase27ToTriSector (PhaseTaggedPart.finePhase tagged)

-- A three-phase assignment can be embedded into the 27-sector grid;
-- the existing tower's section theorem proves recovery of coarse phase.
embedThreePhase : Part → B.TriTruth → PhaseTaggedPart
embedThreePhase p phase = phaseTaggedPart p (Tower.triTo27 phase)

coarseAfterEmbed :
  (p : Part) (phase : B.TriTruth) →
  coarsePhase (embedThreePhase p phase) ≡ phase
coarseAfterEmbed p phase = Tower.triTo27-section phase

-- Component values are input data. Circuit topology is independent of
-- the actual R/C/L values, which can be supplied by each new design.
record SourceBoundCircuit : Set₁ where
  constructor sourceBoundCircuit
  field
    model : Circuit
    attribution : String
    sourceURL : String
    selectedRevision : String
    connectionEvidence : Set
    componentValueEvidence : Set

-- Explicit missing physical semantics: KCL/KVL, constitutive laws,
-- switching, magnetic fields, heat loss and source energy are NOT
-- inferred from the incidence graph.
