module DASHI.Combinatorics.GraphColouring369PantsHomomorphismBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Combinatorics.GraphColouringHomomorphismCoreExact as Colour
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369

------------------------------------------------------------------------
-- 369 / 27-VOXEL / PANTS GRAPH-COLOURING BOUNDARY
--
-- The existing owner gives an exact carrier round-trip
--
--   Ternary27Point <-> PantsPath 3
--
-- and an exact seam flip.  That is enough for a recolouring analogy, but not
-- yet enough for a graph-colouring theorem: neither side currently supplies
-- the graph adjacency relation that would make the carrier maps GraphHom.
--
-- This module records that precise residual rather than inventing adjacency.
------------------------------------------------------------------------

existingTwentySevenPantsRoundTrip : Bool
existingTwentySevenPantsRoundTrip =
  Pants369.ColourWheelNinePantsBoundary.twentySevenIsDepthThreePantsPath
    Pants369.canonicalColourWheelNinePantsBoundary

existingSeamFlip : Bool
existingSeamFlip =
  Pants369.ColourWheelNinePantsBoundary.mobiusActsAsSecondCoordinateSeamFlip
    Pants369.canonicalColourWheelNinePantsBoundary

existingFinitePathIsSmoothSurface : Bool
existingFinitePathIsSmoothSurface =
  Pants369.ColourWheelNinePantsBoundary.finitePantsPathIsSmoothPantsSurface
    Pants369.canonicalColourWheelNinePantsBoundary

------------------------------------------------------------------------
-- What would close the bridge.
------------------------------------------------------------------------

data MissingColouringBridgeLeaf : Set where
  defineTwentySevenAdjacency : MissingColouringBridgeLeaf
  definePantsPathAdjacency : MissingColouringBridgeLeaf
  proveVoxelToPantsPreservesAdjacency : MissingColouringBridgeLeaf
  provePantsToVoxelPreservesAdjacency : MissingColouringBridgeLeaf
  instantiatePaletteGraph : MissingColouringBridgeLeaf
  proveSeamFlipPreservesProperColouring : MissingColouringBridgeLeaf

firstMissingColouringBridgeLeaf : MissingColouringBridgeLeaf
firstMissingColouringBridgeLeaf = defineTwentySevenAdjacency

------------------------------------------------------------------------
-- Fail-closed interpretation.
------------------------------------------------------------------------

record GraphColouring369PantsBoundary : Set where
  constructor graphColouring369PantsBoundary
  field
    twentySevenCarrierRoundTripExists : Bool
    seamFlipExists : Bool
    smoothSurfaceClaimMade : Bool
    twentySevenGraphAdjacencyDefined : Bool
    pantsPathGraphAdjacencyDefined : Bool
    carrierRoundTripUpgradedToGraphIsomorphism : Bool
    seamFlipUpgradedToProperRecolouring : Bool
    firstResidualIsAdjacencyNotAnotherColourOntology : Bool

canonicalGraphColouring369PantsBoundary : GraphColouring369PantsBoundary
canonicalGraphColouring369PantsBoundary =
  graphColouring369PantsBoundary
    existingTwentySevenPantsRoundTrip
    existingSeamFlip
    existingFinitePathIsSmoothSurface
    false
    false
    false
    false
    true

------------------------------------------------------------------------
-- The clean colouring core remains available here as the target interface.
-- We intentionally do not fabricate a `Colour.RelGraph` for the pants carrier
-- until the adjacency semantics are paid by the owning geometry.
------------------------------------------------------------------------

colouringCoreKeepsPantsAdjacencyFailClosed : Bool
colouringCoreKeepsPantsAdjacencyFailClosed =
  Colour.GraphColouringHomomorphismCoreBoundary.pantsAdjacencyInvented
    Colour.canonicalGraphColouringHomomorphismCoreBoundary
