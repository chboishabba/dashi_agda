module DASHI.Physics.Motors.Resonate369SeriesTraceModelExact where

------------------------------------------------------------------------
-- PURE MODEL: hypothetical n+1 series-connected, traversable coils.
-- A 'through coil' edge models electrical traversal between terminal
-- A and B; it does NOT claim short-circuit or zero coil impedance.
-- The graph is an abstract topology, not extracted manufacturer CAD,
-- wiring, or a verified schematic for a real Dodecatron.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Motors.Resonate369SchematicAdmissionExact as S

open S using (Port; port; coil; terminalA; terminalB; Netlist; netlist;
              Reachable; same; edgeStep)

data SeriesEdge : Port → Port → Set where
  throughCoil : (k : Nat) →
    SeriesEdge
      (port (coil k) terminalA)
      (port (coil k) terminalB)
  seriesJunction : (k : Nat) →
    SeriesEdge
      (port (coil k) terminalB)
      (port (coil (suc k)) terminalA)

canonicalSeriesNetlist : Netlist
canonicalSeriesNetlist = netlist SeriesEdge

-- Composition of directed paths; the internal coil step and junction
-- are separately represented, unlike an unjustified single-wire edge.
appendReachable :
  ∀ {p q r} →
  Reachable canonicalSeriesNetlist p q →
  Reachable canonicalSeriesNetlist q r →
  Reachable canonicalSeriesNetlist p r
appendReachable same ys = ys
appendReachable (edgeStep e xs) ys =
  edgeStep e (appendReachable xs ys)

-- There is a directed path across coils 0 through n (inclusive).
canonicalSeriesPath :
  (n : Nat) →
  Reachable canonicalSeriesNetlist
    (port (coil 0) terminalA)
    (port (coil n) terminalB)
canonicalSeriesPath zero = edgeStep (throughCoil zero) same
canonicalSeriesPath (suc n) =
  appendReachable (canonicalSeriesPath n)
    (edgeStep (seriesJunction n)
      (edgeStep (throughCoil (suc n)) same))

-- Twelve coils means indices 0..11, not a hidden thirteenth coil.
twelveCoilSeriesPath :
  Reachable canonicalSeriesNetlist
    (port (coil 0) terminalA)
    (port (coil 11) terminalB)
twelveCoilSeriesPath = canonicalSeriesPath 11

-- We do NOT construct a SelectedSeriesTrace for holmstromDodecatron:
-- that would require a selected actual source and a bypass check.
-- We have only constructed a topology that CAN realise the claim.
