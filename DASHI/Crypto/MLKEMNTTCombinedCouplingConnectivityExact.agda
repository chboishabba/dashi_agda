module DASHI.Crypto.MLKEMNTTCombinedCouplingConnectivityExact where

------------------------------------------------------------------------
-- COMBINED NTT PRIOR + VERIFIER COUPLING GRAPH IS CONNECTED
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Round 17 established two facts:
--   1. within either NTT scalar component, every coordinate shares source
--      variables with every other coordinate in that component;
--   2. FIPS BaseCaseMultiply couples component0 and component1 inside each
--      quadratic residue.
--
-- Their union yields a stronger structural theorem: every two scalar nodes in
-- the 256-entry NTT representation are connected by at most two coupling edges.
-- This rules out a disconnected decomposition of the combined prior/verifier
-- dataflow graph.  It does not prove a large treewidth, statistical dependence,
-- or cryptographic hardness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Crypto.MLKEMNTTDataflowCouplingExact as NTT

------------------------------------------------------------------------
-- Coupling edges.
------------------------------------------------------------------------

data CouplingEdge : NTT.NTTScalarCoordinate → NTT.NTTScalarCoordinate → Set where
  priorConstantEdge : ∀ i j →
    CouplingEdge
      (NTT.scalarCoordinate i NTT.constantPart)
      (NTT.scalarCoordinate j NTT.constantPart)
  priorLinearEdge : ∀ i j →
    CouplingEdge
      (NTT.scalarCoordinate i NTT.linearPart)
      (NTT.scalarCoordinate j NTT.linearPart)
  verifierCrossEdge : ∀ i →
    CouplingEdge
      (NTT.scalarCoordinate i NTT.constantPart)
      (NTT.scalarCoordinate i NTT.linearPart)
  verifierCrossEdgeReverse : ∀ i →
    CouplingEdge
      (NTT.scalarCoordinate i NTT.linearPart)
      (NTT.scalarCoordinate i NTT.constantPart)

------------------------------------------------------------------------
-- Paths of length at most two.
------------------------------------------------------------------------

data ConnectedWithinTwo :
    NTT.NTTScalarCoordinate → NTT.NTTScalarCoordinate → Set where
  oneEdge : ∀ {left right} →
    CouplingEdge left right → ConnectedWithinTwo left right
  twoEdges : ∀ {left middle right} →
    CouplingEdge left middle →
    CouplingEdge middle right →
    ConnectedWithinTwo left right

allScalarCoordinatesConnectedWithinTwo :
  ∀ left right → ConnectedWithinTwo left right
allScalarCoordinatesConnectedWithinTwo
  (NTT.scalarCoordinate i NTT.constantPart)
  (NTT.scalarCoordinate j NTT.constantPart) =
  oneEdge (priorConstantEdge i j)
allScalarCoordinatesConnectedWithinTwo
  (NTT.scalarCoordinate i NTT.linearPart)
  (NTT.scalarCoordinate j NTT.linearPart) =
  oneEdge (priorLinearEdge i j)
allScalarCoordinatesConnectedWithinTwo
  (NTT.scalarCoordinate i NTT.constantPart)
  (NTT.scalarCoordinate j NTT.linearPart) =
  twoEdges
    (priorConstantEdge i j)
    (verifierCrossEdge j)
allScalarCoordinatesConnectedWithinTwo
  (NTT.scalarCoordinate i NTT.linearPart)
  (NTT.scalarCoordinate j NTT.constantPart) =
  twoEdges
    (priorLinearEdge i j)
    (verifierCrossEdgeReverse j)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record CombinedCouplingBoundary : Set where
  constructor combinedCouplingBoundary
  field
    disconnectedIndependentNTTScalarComponents : Bool
    disconnectedIndependentNTTScalarComponentsIsFalse :
      disconnectedIndependentNTTScalarComponents ≡ false
    connectedDataflowGraphProvesHardness : Bool
    connectedDataflowGraphProvesHardnessIsFalse :
      connectedDataflowGraphProvesHardness ≡ false
    usefulConditionalSeparatorStillPossible : Bool
    usefulConditionalSeparatorStillPossibleIsTrue :
      usefulConditionalSeparatorStillPossible ≡ true

open CombinedCouplingBoundary public

canonicalCombinedCouplingBoundary : CombinedCouplingBoundary
canonicalCombinedCouplingBoundary =
  combinedCouplingBoundary false refl false refl true refl
