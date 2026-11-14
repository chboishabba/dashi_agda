module DASHI.Physics.Motors.FilsingerLydenCircuit36927AdapterExact where

-- A THIN ADAPTER to existing PR #1482's common component/pin/wire model.
-- SOURCE RULES: candidate netlist ≠ observed physical connectivity;
-- narrated connection ≠ independently traced conductor;
-- visible voltage / acoustic frequency ≠ environmental real power.
-- No vendor file, geometry, antenna, switching frequency or power gain asserted.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as G

-- Stable names for the selected circuit-model nodes (not physical locations).
whiteCapId blueCapId driveId toroidId earthId : Nat
whiteCapId = 0
blueCapId = 1
driveId = 2
toroidId = 3
earthId = 4

-- Only 3.33 microfarad is explicitly identified in the recording.
-- 2 microfarad, 10kV for the blue capacitor is a tentative label reading.
-- No switching inductance or source current is asserted.
whiteCap : G.Part
whiteCap = G.part whiteCapId G.capacitor "White 3.33uF narrated" (G.picofarads 3330000) 2

blueCapCandidate : G.Part
blueCapCandidate = G.part blueCapId G.capacitor "Blue capacitor tentative 2uF" (G.picofarads 2000000) 2

driveCandidate : G.Part
driveCandidate = G.part driveId G.voltageSource "Reported 15V input" (G.millivolts 15000) 2

toroidCandidate : G.Part
toroidCandidate = G.part toroidId G.inductor "Toroidal winding: topology unknown" G.unavailable 2

earthCandidate : G.Part
earthCandidate = G.part earthId G.groundPoint "Narrated earth-negative" G.unavailable 1

-- Source narrows the selected connection to hot-side -> Earth-negative.
-- It does NOT identify the cap's manufacturer's terminal number or a
-- measured wire trace. Terminal 0 is a LOCAL MODEL CONVENTION only.
hot : G.Endpoint
hot = G.atPin (G.pin whiteCapId zero)

earthNegative : G.Endpoint
earthNegative = G.atPin (G.pin earthId zero)

narratedEdge : G.Wire
narratedEdge = G.wire hot earthNegative

-- This circuit is a *candidate source model* with ONE narrated edge.
-- Everything else remains unconnected rather than fabricated.
partsByIndex : Nat → G.Part
partsByIndex zero = whiteCap
partsByIndex (suc zero) = blueCapCandidate
partsByIndex (suc (suc zero)) = driveCandidate
partsByIndex (suc (suc (suc zero))) = toroidCandidate
partsByIndex _ = earthCandidate

wiresByIndex : Nat → G.Wire
wiresByIndex _ = narratedEdge

filsingerNarrationCandidate : G.Circuit
filsingerNarrationCandidate =
  G.circuit partsByIndex 5 wiresByIndex 1 "2026-11-10 narrated-only revision"

-- An observer may select evidence for a REAL wire only after
-- checking the original footage and/or a physical instrument trace.
record RealConnectionAdmission : Set₁ where
  field
    selectedDeviceRevision : String
    originalMediaReference : String
    WireIsPhysicallyConnected : Set
    measuredOrInspectedWire : WireIsPhysicallyConnected

-- The named wire's endpoints are a definitional property of our
-- candidate representation, not a theorem about unseen wiring.
narratedHotEndpoint : G.Wire.from narratedEdge ≡ hot
narratedHotEndpoint = refl

narratedEarthEndpoint : G.Wire.to narratedEdge ≡ earthNegative
narratedEarthEndpoint = refl

-- Reuse shared graph-route machinery. Any route needs actual Edge
-- evidence from a selected wiring graph; it is never inferred from
-- the parts inventory, source attribution, or a meter reading.
reportedEdgeYieldsCandidateRoute :
  (g : G.WiringGraph) →
  G.WiringGraph.Edge g hot earthNegative →
  G.Route g hot earthNegative
reportedEdgeYieldsCandidateRoute g edge = G.step edge G.here

-- Distinguish a source-/meter-validated signal path from a physical
-- environmental energy source. Do not inhabit this record with strings.
record PhysicalEarthPortClosure : Set₁ where
  field
    SelectedElectricalClock : Set
    MeasuredInputRealPower : Set
    SignedEarthPortRealPower : Set
    AllStorageAndLosses : Set
    SignedMeterTerminalReference : Set
    electricalClock : SelectedElectricalClock
    powerInput : MeasuredInputRealPower
    earthPower : SignedEarthPortRealPower
    energyBudget : AllStorageAndLosses
    signedPolarity : SignedMeterTerminalReference

-- 3/9/27 phase assignment and A* are in the imported generic owners;
-- no physical phasing or shortest electric-current path is inferred here.
