{-# OPTIONS --safe #-}
module DASHI.Combinatorics.GraphColouring369PantsGridAdjacencyExact where

------------------------------------------------------------------------
-- EXACT 27-GRID <-> DEPTH-THREE PANTS GRAPH HOMOMORPHISMS.
--
-- Reuse-first: Geometry already owns the trit nearest-neighbour step
-- (-1 <-> 0 <-> +1) and the 27-grid adjacency; Pants369 already owns
-- the two-sided voxel/path equivalence.  GraphColouringHomomorphismCore
-- already owns GraphHom and pullback of proper colourings.
--
-- The slot graph is a *declared finite graph*.  Neither its adjacency nor
-- any recolouring constructs a continuous/smooth pair-of-pants surface.
--
-- Source vocabulary: M. F. Atiyah, Topological quantum field theory,
-- Publ. Math. IHES 68 (1988), DOI 10.1007/BF02698547.
-- Mathematical/Agda adapter and explicit finite grid proofs: DASHI.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Combinatorics.GraphColouringHomomorphismCoreExact as Colour
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral

------------------------------------------------------------------------
-- 1. Independent, source-grounded slot adjacency (NOT arbitrary unequal
--    coordinates): 3--6 and 6--9, but never direct 3--9.
------------------------------------------------------------------------

slotToSSP : Pants.BranchSlot -> SSP.SSPTrit
slotToSSP s = Pants369.kernelToSSP (Pants369.slotToKernel s)

sspToSlot : SSP.SSPTrit -> Pants.BranchSlot
sspToSlot x = Pants369.kernelToSlot (Pants369.sspToKernel x)

slotSSPRoundTrip : (s : Pants.BranchSlot) ->
  sspToSlot (slotToSSP s) ≡ s
slotSSPRoundTrip Pants.slot3 = refl
slotSSPRoundTrip Pants.slot6 = refl
slotSSPRoundTrip Pants.slot9 = refl

sspSlotRoundTrip : (x : SSP.SSPTrit) ->
  slotToSSP (sspToSlot x) ≡ x
sspSlotRoundTrip SSP.sspNegOne = refl
sspSlotRoundTrip SSP.sspZero = refl
sspSlotRoundTrip SSP.sspPosOne = refl

SlotGridStep : Pants.BranchSlot -> Pants.BranchSlot -> Set
SlotGridStep a b = Geometry.TritGridStep (slotToSSP a) (slotToSSP b)

slotStepFromTrit :
  ∀ {a b} -> Geometry.TritGridStep a b ->
  SlotGridStep (sspToSlot a) (sspToSlot b)
slotStepFromTrit {a} {b} step
  rewrite sspSlotRoundTrip a | sspSlotRoundTrip b = step

noDirectSlot3To9 : SlotGridStep Pants.slot3 Pants.slot9 -> ⊥
noDirectSlot3To9 = Geometry.noDirectNegToPos

------------------------------------------------------------------------
-- 2. Exactly one nearest-neighbour coordinate changes.
------------------------------------------------------------------------

data Pants3Adjacent :
  Frontier.PantsPath 3 -> Frontier.PantsPath 3 -> Set where
  pantsAdjacentX : ∀ {a b c d} -> SlotGridStep a b ->
    Pants3Adjacent
      (a vcons c vcons d vcons vnil)
      (b vcons c vcons d vcons vnil)
  pantsAdjacentY : ∀ {a b c d} -> SlotGridStep b c ->
    Pants3Adjacent
      (a vcons b vcons d vcons vnil)
      (a vcons c vcons d vcons vnil)
  pantsAdjacentZ : ∀ {a b c d} -> SlotGridStep c d ->
    Pants3Adjacent
      (a vcons b vcons c vcons vnil)
      (a vcons b vcons d vcons vnil)

voxelGrid : Colour.RelGraph
voxelGrid = Colour.relGraph
  Geometry.Ternary27Point Geometry.HypervoxelAdjacent

pantsGrid : Colour.RelGraph
pantsGrid = Colour.relGraph
  (Frontier.PantsPath 3) Pants3Adjacent

------------------------------------------------------------------------
-- 3. Both directions preserve actual declared adjacency.
------------------------------------------------------------------------

voxelToPantsPreservesAdj :
  ∀ {u v} -> Geometry.HypervoxelAdjacent u v ->
  Pants3Adjacent (Pants369.voxel27ToPants3 u)
                 (Pants369.voxel27ToPants3 v)
voxelToPantsPreservesAdj (Geometry.adjacentX step) =
  pantsAdjacentX (slotStepFromTrit step)
voxelToPantsPreservesAdj (Geometry.adjacentY step) =
  pantsAdjacentY (slotStepFromTrit step)
voxelToPantsPreservesAdj (Geometry.adjacentZ step) =
  pantsAdjacentZ (slotStepFromTrit step)

pantsToVoxelPreservesAdj :
  ∀ {p q} -> Pants3Adjacent p q ->
  Geometry.HypervoxelAdjacent
    (Pants369.pants3ToVoxel27 p)
    (Pants369.pants3ToVoxel27 q)
pantsToVoxelPreservesAdj (pantsAdjacentX step) =
  Geometry.adjacentX step
pantsToVoxelPreservesAdj (pantsAdjacentY step) =
  Geometry.adjacentY step
pantsToVoxelPreservesAdj (pantsAdjacentZ step) =
  Geometry.adjacentZ step

voxelToPantsGraphHom : Colour.GraphHom voxelGrid pantsGrid
voxelToPantsGraphHom =
  Colour.graphHom Pants369.voxel27ToPants3 voxelToPantsPreservesAdj

pantsToVoxelGraphHom : Colour.GraphHom pantsGrid voxelGrid
pantsToVoxelGraphHom =
  Colour.graphHom Pants369.pants3ToVoxel27 pantsToVoxelPreservesAdj

voxelGraphHomRoundTrip : (u : Geometry.Ternary27Point) ->
  Colour.onVertex
    (Colour.composeHom voxelToPantsGraphHom pantsToVoxelGraphHom) u ≡ u
voxelGraphHomRoundTrip = Pants369.voxelPantsRoundTrip

pantsGraphHomRoundTrip : (p : Frontier.PantsPath 3) ->
  Colour.onVertex
    (Colour.composeHom pantsToVoxelGraphHom voxelToPantsGraphHom) p ≡ p
pantsGraphHomRoundTrip = Pants369.pantsVoxelRoundTrip

------------------------------------------------------------------------
-- 4. Explicit geometric C3 automorphism: coordinate ROTATION is genuine
--    for the unweighted nearest-neighbour geometry.  This does NOT imply
--    the image's asymmetric weighted matrix carries such an action.
------------------------------------------------------------------------

rotatePants : Frontier.PantsPath 3 -> Frontier.PantsPath 3
rotatePants (a vcons b vcons c vcons vnil) =
  b vcons c vcons a vcons vnil

rotatePantsPreservesAdj : ∀ {p q} ->
  Pants3Adjacent p q ->
  Pants3Adjacent (rotatePants p) (rotatePants q)
rotatePantsPreservesAdj (pantsAdjacentX step) = pantsAdjacentZ step
rotatePantsPreservesAdj (pantsAdjacentY step) = pantsAdjacentX step
rotatePantsPreservesAdj (pantsAdjacentZ step) = pantsAdjacentY step

rotatePantsOrderThree :
  (p : Frontier.PantsPath 3) ->
  rotatePants (rotatePants (rotatePants p)) ≡ p
rotatePantsOrderThree (a vcons b vcons c vcons vnil) = refl

voxelPantsRotateCommutes : (u : Geometry.Ternary27Point) ->
  rotatePants (Pants369.voxel27ToPants3 u) ≡
  Pants369.voxel27ToPants3 (Spectral.rotateXYZ u)
voxelPantsRotateCommutes (Geometry.ternary27Point x y z) = refl

rotatePantsGraphHom : Colour.GraphHom pantsGrid pantsGrid
rotatePantsGraphHom = Colour.graphHom rotatePants rotatePantsPreservesAdj

------------------------------------------------------------------------
-- 5. The declared second-coordinate flip is a graph automorphism of the
--    nearest-neighbour finite grid.  It is NOT a claim about smooth pants
--    topology, analytic modular transport, or arbitrary weighted edges.
------------------------------------------------------------------------

flipSlot : Pants.BranchSlot -> Pants.BranchSlot
flipSlot Pants.slot3 = Pants.slot9
flipSlot Pants.slot6 = Pants.slot6
flipSlot Pants.slot9 = Pants.slot3

flipSlotInvolutive : (s : Pants.BranchSlot) ->
  flipSlot (flipSlot s) ≡ s
flipSlotInvolutive Pants.slot3 = refl
flipSlotInvolutive Pants.slot6 = refl
flipSlotInvolutive Pants.slot9 = refl

flipSSP : SSP.SSPTrit -> SSP.SSPTrit
flipSSP SSP.sspNegOne = SSP.sspPosOne
flipSSP SSP.sspZero = SSP.sspZero
flipSSP SSP.sspPosOne = SSP.sspNegOne

flipSlotCommutes : (s : Pants.BranchSlot) ->
  slotToSSP (flipSlot s) ≡ flipSSP (slotToSSP s)
flipSlotCommutes Pants.slot3 = refl
flipSlotCommutes Pants.slot6 = refl
flipSlotCommutes Pants.slot9 = refl

flipSSPStep : ∀ {x y} -> Geometry.TritGridStep x y ->
  Geometry.TritGridStep (flipSSP x) (flipSSP y)
flipSSPStep Geometry.negToZero = Geometry.posToZero
flipSSPStep Geometry.zeroToNeg = Geometry.zeroToPos
flipSSPStep Geometry.zeroToPos = Geometry.zeroToNeg
flipSSPStep Geometry.posToZero = Geometry.negToZero

flipSlotStep : ∀ {a b} -> SlotGridStep a b ->
  SlotGridStep (flipSlot a) (flipSlot b)
flipSlotStep {a} {b} step
  rewrite flipSlotCommutes a | flipSlotCommutes b =
    flipSSPStep step

flipSecondPants : Frontier.PantsPath 3 -> Frontier.PantsPath 3
flipSecondPants (a vcons b vcons c vcons vnil) =
  a vcons flipSlot b vcons c vcons vnil

flipSecondPantsInvolutive : (p : Frontier.PantsPath 3) ->
  flipSecondPants (flipSecondPants p) ≡ p
flipSecondPantsInvolutive (a vcons b vcons c vcons vnil)
  rewrite flipSlotInvolutive b = refl

flipSecondPreservesAdj : ∀ {p q} ->
  Pants3Adjacent p q ->
  Pants3Adjacent (flipSecondPants p) (flipSecondPants q)
flipSecondPreservesAdj (pantsAdjacentX step) =
  pantsAdjacentX step
flipSecondPreservesAdj (pantsAdjacentY step) =
  pantsAdjacentY (flipSlotStep step)
flipSecondPreservesAdj (pantsAdjacentZ step) =
  pantsAdjacentZ step

flipPantsGraphHom : Colour.GraphHom pantsGrid pantsGrid
flipPantsGraphHom = Colour.graphHom flipSecondPants flipSecondPreservesAdj

-- Recolouring an arbitrary existing proper palette colouring is a
-- contravariant pullback. No chromatic-number optimality is claimed.
pullbackProperColouringThroughFlip :
  ∀ {Palette : Colour.RelGraph} ->
  Colour.Colouring pantsGrid Palette ->
  Colour.Colouring pantsGrid Palette
pullbackProperColouringThroughFlip =
  Colour.pullbackColouring flipPantsGraphHom

pullbackProperColouringThroughRotation :
  ∀ {Palette : Colour.RelGraph} ->
  Colour.Colouring pantsGrid Palette ->
  Colour.Colouring pantsGrid Palette
pullbackProperColouringThroughRotation =
  Colour.pullbackColouring rotatePantsGraphHom

-- A selected proper palette instance: the existing voxel adjacency itself.
-- This is a 27-label palette, NOT a minimum colouring or four-colour proof.
selectedPalette : Colour.RelGraph
selectedPalette = voxelGrid

selectedPantsColouring : Colour.Colouring pantsGrid selectedPalette
selectedPantsColouring = pantsToVoxelGraphHom

selectedFlippedColouring : Colour.Colouring pantsGrid selectedPalette
selectedFlippedColouring =
  pullbackProperColouringThroughFlip selectedPantsColouring
