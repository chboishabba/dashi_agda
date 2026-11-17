module DASHI.Biology.IITXORGridFibreCircuitBridgeExact where

------------------------------------------------------------------------
-- XOR GRID AS REPEATED LOCAL SYNTHESIS CELLS + CAUSAL GLUING CIRCUITS
--
-- The existing 2x2 XOR fixture already specifies each successor site as XOR of
-- two predecessor sites.  This module exposes its dependency graph explicitly.
--
-- Gate semantics and wiring remain separate:
--   * each target site owns a local 2 -> 1 XOR synthesis;
--   * directed source -> target dependencies are the gluing/fabric edges;
--   * closed directed paths are recurrence witnesses of the fabric.
--
-- Thus the grid's circuits are not themselves XOR operations.  XOR is the
-- local algebra carried at the trivalent cells joined by those circuits.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as XOR
import DASHI.Biology.IITXORGridAdversarialExact as Grid
import DASHI.Biology.IITCausalPantsFibreGluingExact as Pants

------------------------------------------------------------------------
-- 1. Four grid sites and the exact source -> target dependency edges.
------------------------------------------------------------------------

data GridSite : Set where
  northWestSite : GridSite
  northEastSite : GridSite
  southWestSite : GridSite
  southEastSite : GridSite

data GridCausalEdge : GridSite → GridSite → Set where
  northEastToNorthWest : GridCausalEdge northEastSite northWestSite
  southWestToNorthWest : GridCausalEdge southWestSite northWestSite

  northWestToNorthEast : GridCausalEdge northWestSite northEastSite
  southEastToNorthEast : GridCausalEdge southEastSite northEastSite

  northWestToSouthWest : GridCausalEdge northWestSite southWestSite
  southEastToSouthWest : GridCausalEdge southEastSite southWestSite

  northEastToSouthEast : GridCausalEdge northEastSite southEastSite
  southWestToSouthEast : GridCausalEdge southWestSite southEastSite

------------------------------------------------------------------------
-- 2. Every successor coordinate is literally the existing XOR of its two
--    incoming predecessor fibres.
------------------------------------------------------------------------

northWestLocalXor :
  (grid : Grid.Grid2x2) →
  Grid.northWest (Grid.gridStep grid)
  ≡ XOR.xor (Grid.northEast grid) (Grid.southWest grid)
northWestLocalXor grid = refl

northEastLocalXor :
  (grid : Grid.Grid2x2) →
  Grid.northEast (Grid.gridStep grid)
  ≡ XOR.xor (Grid.northWest grid) (Grid.southEast grid)
northEastLocalXor grid = refl

southWestLocalXor :
  (grid : Grid.Grid2x2) →
  Grid.southWest (Grid.gridStep grid)
  ≡ XOR.xor (Grid.northWest grid) (Grid.southEast grid)
southWestLocalXor grid = refl

southEastLocalXor :
  (grid : Grid.Grid2x2) →
  Grid.southEast (Grid.gridStep grid)
  ≡ XOR.xor (Grid.northEast grid) (Grid.southWest grid)
southEastLocalXor grid = refl

------------------------------------------------------------------------
-- 3. Exact recurrence witnesses live in the dependency/gluing graph.
------------------------------------------------------------------------

record TwoEdgeCircuit (left right : GridSite) : Set where
  constructor two-edge-circuit
  field
    forwardEdge : GridCausalEdge left right
    backwardEdge : GridCausalEdge right left
open TwoEdgeCircuit public

northWestNorthEastCircuit : TwoEdgeCircuit northWestSite northEastSite
northWestNorthEastCircuit =
  two-edge-circuit northWestToNorthEast northEastToNorthWest

northWestSouthWestCircuit : TwoEdgeCircuit northWestSite southWestSite
northWestSouthWestCircuit =
  two-edge-circuit northWestToSouthWest southWestToNorthWest

southEastNorthEastCircuit : TwoEdgeCircuit southEastSite northEastSite
southEastNorthEastCircuit =
  two-edge-circuit southEastToNorthEast northEastToSouthEast

southEastSouthWestCircuit : TwoEdgeCircuit southEastSite southWestSite
southEastSouthWestCircuit =
  two-edge-circuit southEastToSouthWest southWestToSouthEast

------------------------------------------------------------------------
-- 4. The generic pants/fibre owner gives the interpretation boundary:
--    recurrence belongs to gluing topology, local XOR belongs to synthesis.
------------------------------------------------------------------------

causalPantsBoundary : Pants.IITCausalPantsFibreBoundary
causalPantsBoundary = Pants.canonicalIITCausalPantsFibreBoundary

gridCircuitIsNotLocalGate :
  Pants.gluingIsLocalGateByDefinition causalPantsBoundary ≡ false
gridCircuitIsNotLocalGate = Pants.gluingIsNotGate

record XORGridFibreCircuitBoundary : Set where
  constructor xor-grid-fibre-circuit-boundary
  field
    fourLocalXorCellsExposed : Bool
    directedDependencyEdgesExposed : Bool
    explicitTwoEdgeCircuitsExist : Bool
    recurrenceLivesInGridGluingGraph : Bool
    localXorOperationEqualsCircuitByDefinition : Bool
    graphCircuitAloneDeterminesIITPhi : Bool

open XORGridFibreCircuitBoundary public

canonicalXORGridFibreCircuitBoundary : XORGridFibreCircuitBoundary
canonicalXORGridFibreCircuitBoundary =
  xor-grid-fibre-circuit-boundary
    true true true true false false

xorAndCircuitRemainSeparate :
  localXorOperationEqualsCircuitByDefinition
    canonicalXORGridFibreCircuitBoundary ≡ false
xorAndCircuitRemainSeparate = refl

circuitAloneDoesNotDeterminePhi :
  graphCircuitAloneDeterminesIITPhi
    canonicalXORGridFibreCircuitBoundary ≡ false
circuitAloneDoesNotDeterminePhi = refl
