module DASHI.Combinatorics.GraphColouring369PantsHomomorphismBoundaryExact where
import DASHI.Combinatorics.GraphColouring369PantsSymmetryCutInvariantExact as S3Cut369
import DASHI.Combinatorics.GraphColouring369PantsEdgeCoverageExact as EdgeChart369

open import DASHI.Core.Prelude

import DASHI.Combinatorics.GraphColouringHomomorphismCoreExact as Colour
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369
import DASHI.Combinatorics.GraphColouring369PantsGridAdjacencyExact as Grid

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

------------------------------------------------------------------------
-- 2026-10-30 source-written finite closure candidate (kernel pending).
--
-- Existing status flags above intentionally remain conservative until an
-- exact-head Agda safe-mode receipt is produced.  These new typed terms
-- consume the actual Geometry.HypervoxelAdjacent, NOT an invented relation.
------------------------------------------------------------------------

nativeVoxelGrid : Colour.RelGraph
nativeVoxelGrid = Grid.voxelGrid

nativePantsGrid : Colour.RelGraph
nativePantsGrid = Grid.pantsGrid

nativeVoxelToPantsGraphHom :
  Colour.GraphHom nativeVoxelGrid nativePantsGrid
nativeVoxelToPantsGraphHom = Grid.voxelToPantsGraphHom

nativePantsToVoxelGraphHom :
  Colour.GraphHom nativePantsGrid nativeVoxelGrid
nativePantsToVoxelGraphHom = Grid.pantsToVoxelGraphHom

nativeC3PantsAutomorphism :
  Colour.GraphHom nativePantsGrid nativePantsGrid
nativeC3PantsAutomorphism = Grid.rotatePantsGraphHom

nativeSecondSeamFlipGraphAutomorphism :
  Colour.GraphHom nativePantsGrid nativePantsGrid
nativeSecondSeamFlipGraphAutomorphism = Grid.flipPantsGraphHom

nativeSelectedColouring :
  Colour.Colouring nativePantsGrid Grid.selectedPalette
nativeSelectedColouring = Grid.selectedPantsColouring

nativeFlipPreservesProperColouring :
  Colour.Colouring nativePantsGrid Grid.selectedPalette
nativeFlipPreservesProperColouring = Grid.selectedFlippedColouring

record GraphColouring369PantsSourceWrittenCandidate : Set where
  constructor graph-colouring-369-pants-source-written-candidate
  field
    geometryAdjacencyReused : Bool
    pathAdjacencyExplicit : Bool
    bothGraphHomTermsWritten : Bool
    C3RotationGraphHomWritten : Bool
    seamFlipGraphHomWritten : Bool
    selectedPaletteColouringWritten : Bool
    exactHeadAgdaKernelChecked : Bool
    smoothPantsSurfaceEstablished : Bool
    minimumColourCountEstablished : Bool

currentGraphColouring369PantsSourceWrittenCandidate :
  GraphColouring369PantsSourceWrittenCandidate
currentGraphColouring369PantsSourceWrittenCandidate =
  graph-colouring-369-pants-source-written-candidate
    true true true true true true false false false
