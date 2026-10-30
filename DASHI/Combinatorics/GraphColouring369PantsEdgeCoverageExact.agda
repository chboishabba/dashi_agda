{-# OPTIONS --safe #-}
module DASHI.Combinatorics.GraphColouring369PantsEdgeCoverageExact where

------------------------------------------------------------------------
-- NATIVE 27-GRID EDGE ORIENTATION NORMAL FORM, NOT A NEW GRAPH.
--
-- Reuses Geometry.HypervoxelAdjacent and the exact 54 native unit
-- edges in GraphColouring369PantsWeightedMaxCutExact.
--
-- Every oriented native edge factors as a canonical forward slot or
-- the reversal of one. The 54 canonical slots enumerate three axes,
-- three-by-three fixed coordinates and two directed increasing steps:
--
--         3 axes × 3 × 3 × 2 = 54.
--
-- The slot index list 0..53 is a closed, exact computation. A fully
-- generalized theorem that slotId is injective, or that a returned
-- list's equality implies edge identity, is *not* promoted here.
--
-- This is discrete combinatorics, not smooth pants, physical topology,
-- empirical directionality, or Monster representation identity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List using (map; concatMap; length; _++_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Combinatorics.GraphColouring369PantsWeightedMaxCutExact as Cut

data PositiveStep : Set where
  lowerStep upperStep : PositiveStep

data NativeEdgeSlot : Set where
  slotX : SSP.SSPTrit -> SSP.SSPTrit -> PositiveStep -> NativeEdgeSlot
  slotY : SSP.SSPTrit -> SSP.SSPTrit -> PositiveStep -> NativeEdgeSlot
  slotZ : SSP.SSPTrit -> SSP.SSPTrit -> PositiveStep -> NativeEdgeSlot

data Orientation : Set where
  increasing decreasing : Orientation

open Cut.NativeWeightedEdge using (source; target; adjacent; weight)

slotEdge : NativeEdgeSlot -> Cut.NativeWeightedEdge
slotEdge (slotX y z lowerStep) =
  Cut.native-weighted-edge
    (Geometry.ternary27Point SSP.sspNegOne y z)
    (Geometry.ternary27Point SSP.sspZero y z)
    (Geometry.adjacentX Geometry.negToZero) 1
slotEdge (slotX y z upperStep) =
  Cut.native-weighted-edge
    (Geometry.ternary27Point SSP.sspZero y z)
    (Geometry.ternary27Point SSP.sspPosOne y z)
    (Geometry.adjacentX Geometry.zeroToPos) 1
slotEdge (slotY x z lowerStep) =
  Cut.native-weighted-edge
    (Geometry.ternary27Point x SSP.sspNegOne z)
    (Geometry.ternary27Point x SSP.sspZero z)
    (Geometry.adjacentY Geometry.negToZero) 1
slotEdge (slotY x z upperStep) =
  Cut.native-weighted-edge
    (Geometry.ternary27Point x SSP.sspZero z)
    (Geometry.ternary27Point x SSP.sspPosOne z)
    (Geometry.adjacentY Geometry.zeroToPos) 1
slotEdge (slotZ x y lowerStep) =
  Cut.native-weighted-edge
    (Geometry.ternary27Point x y SSP.sspNegOne)
    (Geometry.ternary27Point x y SSP.sspZero)
    (Geometry.adjacentZ Geometry.negToZero) 1
slotEdge (slotZ x y upperStep) =
  Cut.native-weighted-edge
    (Geometry.ternary27Point x y SSP.sspZero)
    (Geometry.ternary27Point x y SSP.sspPosOne)
    (Geometry.adjacentZ Geometry.zeroToPos) 1

slotSource : NativeEdgeSlot -> Geometry.Ternary27Point
slotSource s = source (slotEdge s)

slotTarget : NativeEdgeSlot -> Geometry.Ternary27Point
slotTarget s = target (slotEdge s)

chartSource : NativeEdgeSlot -> Orientation -> Geometry.Ternary27Point
chartSource slot increasing = slotSource slot
chartSource slot decreasing = slotTarget slot

chartTarget : NativeEdgeSlot -> Orientation -> Geometry.Ternary27Point
chartTarget slot increasing = slotTarget slot
chartTarget slot decreasing = slotSource slot

record OrientedSlotCertificate
  (u v : Geometry.Ternary27Point) : Set where
  constructor oriented-slot-certificate
  field
    slot : NativeEdgeSlot
    orientation : Orientation
    sourceExact : chartSource slot orientation ≡ u
    targetExact : chartTarget slot orientation ≡ v

open OrientedSlotCertificate public

-- Exhausts all four native TritGridStep constructors on each of
-- the three axes. This is an explicit completeness witness for the
-- actual pre-existing Geometry.HypervoxelAdjacent constructors.
classifyNativeAdjacency :
  ∀ {u v} -> Geometry.HypervoxelAdjacent u v ->
  OrientedSlotCertificate u v
classifyNativeAdjacency
  (Geometry.adjacentX {y0 = y} {z0 = z} Geometry.negToZero) =
  oriented-slot-certificate (slotX y z lowerStep) increasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentX {y0 = y} {z0 = z} Geometry.zeroToNeg) =
  oriented-slot-certificate (slotX y z lowerStep) decreasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentX {y0 = y} {z0 = z} Geometry.zeroToPos) =
  oriented-slot-certificate (slotX y z upperStep) increasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentX {y0 = y} {z0 = z} Geometry.posToZero) =
  oriented-slot-certificate (slotX y z upperStep) decreasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentY {x0 = x} {z0 = z} Geometry.negToZero) =
  oriented-slot-certificate (slotY x z lowerStep) increasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentY {x0 = x} {z0 = z} Geometry.zeroToNeg) =
  oriented-slot-certificate (slotY x z lowerStep) decreasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentY {x0 = x} {z0 = z} Geometry.zeroToPos) =
  oriented-slot-certificate (slotY x z upperStep) increasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentY {x0 = x} {z0 = z} Geometry.posToZero) =
  oriented-slot-certificate (slotY x z upperStep) decreasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentZ {x0 = x} {y0 = y} Geometry.negToZero) =
  oriented-slot-certificate (slotZ x y lowerStep) increasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentZ {x0 = x} {y0 = y} Geometry.zeroToNeg) =
  oriented-slot-certificate (slotZ x y lowerStep) decreasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentZ {x0 = x} {y0 = y} Geometry.zeroToPos) =
  oriented-slot-certificate (slotZ x y upperStep) increasing refl refl
classifyNativeAdjacency
  (Geometry.adjacentZ {x0 = x} {y0 = y} Geometry.posToZero) =
  oriented-slot-certificate (slotZ x y upperStep) decreasing refl refl

slotPair : SSP.SSPTrit -> SSP.SSPTrit -> List NativeEdgeSlot
slotPair y z =
  slotX y z lowerStep ∷ slotX y z upperStep ∷ []

slotPairY : SSP.SSPTrit -> SSP.SSPTrit -> List NativeEdgeSlot
slotPairY x z =
  slotY x z lowerStep ∷ slotY x z upperStep ∷ []

slotPairZ : SSP.SSPTrit -> SSP.SSPTrit -> List NativeEdgeSlot
slotPairZ x y =
  slotZ x y lowerStep ∷ slotZ x y upperStep ∷ []

allNativeSlots : List NativeEdgeSlot
allNativeSlots =
  concatMap (λ p -> slotPair (proj₁ p) (proj₂ p)) Cut.allPairs
  ++ concatMap (λ p -> slotPairY (proj₁ p) (proj₂ p)) Cut.allPairs
  ++ concatMap (λ p -> slotPairZ (proj₁ p) (proj₂ p)) Cut.allPairs

allNativeSlotsCount54 : length allNativeSlots ≡ 54
allNativeSlotsCount54 = refl

allNativeSlotsMapToExactExistingEdges :
  map slotEdge allNativeSlots ≡ Cut.unitNativeGridEdges
allNativeSlotsMapToExactExistingEdges = refl

tritIndex : SSP.SSPTrit -> Nat
tritIndex SSP.sspNegOne = 0
tritIndex SSP.sspZero = 1
tritIndex SSP.sspPosOne = 2

stepIndex : PositiveStep -> Nat
stepIndex lowerStep = 0
stepIndex upperStep = 1

slotIndex : NativeEdgeSlot -> Nat
slotIndex (slotX a b s) =
  2 * (3 * tritIndex a + tritIndex b) + stepIndex s
slotIndex (slotY a b s) =
  18 + 2 * (3 * tritIndex a + tritIndex b) + stepIndex s
slotIndex (slotZ a b s) =
  36 + 2 * (3 * tritIndex a + tritIndex b) + stepIndex s

-- Every identifier appears once *in this particular closed slot list*.
-- This evaluated equality is not silently upgraded into a generic
-- property of all Nat or an unproved code-injectivity theorem.
closedSlotIdentifierCensus :
  map slotIndex allNativeSlots ≡
  0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ 17 ∷ 18 ∷ 19 ∷ 20 ∷ 21 ∷ 22 ∷ 23 ∷ 24 ∷ 25 ∷ 26 ∷ 27 ∷ 28 ∷ 29 ∷ 30 ∷ 31 ∷ 32 ∷ 33 ∷ 34 ∷ 35 ∷ 36 ∷ 37 ∷ 38 ∷ 39 ∷ 40 ∷ 41 ∷ 42 ∷ 43 ∷ 44 ∷ 45 ∷ 46 ∷ 47 ∷ 48 ∷ 49 ∷ 50 ∷ 51 ∷ 52 ∷ 53 ∷ []
closedSlotIdentifierCensus = refl

record EdgeChartCoverageBoundary : Set where
  constructor edge-chart-coverage-boundary
  field
    everyActualNativeAdjacencyHasChart : Bool
    actualConstructorsExhausted : Bool
    exact54CanonicalSlots : Bool
    exactExistingEdgeListRoundTrip : Bool
    exactZeroToFiftyThreeIdentifierCensus : Bool
    slotIdInjectivityEstablishedHere : Bool
    exactHeadAgdaKernelChecked : Bool
    smoothOrPhysicalPantsClaimed : Bool

canonicalEdgeChartCoverageBoundary : EdgeChartCoverageBoundary
canonicalEdgeChartCoverageBoundary =
  edge-chart-coverage-boundary true true true true true false false false
