{-# OPTIONS --safe #-}
module DASHI.Combinatorics.GraphColouring369PantsWeightedMaxCutExact where

------------------------------------------------------------------------
-- Native ternary 27-grid: a SATURATING MAXIMUM CUT.
--
-- Reuse the golden native adjacency and checkerboard two-colouring.
-- Every native edge crosses the selected cut, so for any FINITE list
-- of witnessed native edges and arbitrary NAT (nonnegative) weights,
-- the cut has maximum possible weight.
--
-- This is a nontrivial finite graph theorem; NOT an assertion that
-- arbitrary MAX-CUT is easy, or that a 3-node asymmetric directed
-- graph has the same edge structure.  This does NOT claim a smooth
-- pants surface, social causal inference, or a Monster representation.
--
-- Primary graph-theoretic concepts: standard graph bipartition and
-- maximum-cut definitions; DASHI owns this finite formal adapter.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List using (map; concatMap; length; _++_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Combinatorics.GraphColouring369PantsGridAdjacencyExact as Grid

Point : Set
Point = Geometry.Ternary27Point

Partition : Set
Partition = Point -> Bool

record NativeWeightedEdge : Set where
  constructor native-weighted-edge
  field
    source target : Point
    adjacent : Geometry.HypervoxelAdjacent source target
    weight : Nat
open NativeWeightedEdge public

differentBit : Bool -> Bool -> Bool
differentBit = Grid.xorBool

cutBit : Partition -> NativeWeightedEdge -> Bool
cutBit partition e = differentBit (partition (source e)) (partition (target e))

edgeScore : Partition -> NativeWeightedEdge -> Nat
edgeScore partition e with cutBit partition e
... | true = weight e
... | false = zero

edgeScoreBound : (partition : Partition) (e : NativeWeightedEdge) ->
  edgeScore partition e ≤ weight e
edgeScoreBound partition e with cutBit partition e
... | true = ≤-refl
... | false = z≤n

cutScore : Partition -> List NativeWeightedEdge -> Nat
cutScore partition [] = zero
cutScore partition (e ∷ edges) =
  edgeScore partition e + cutScore partition edges

totalWeight : List NativeWeightedEdge -> Nat
totalWeight [] = zero
totalWeight (e ∷ edges) = weight e + totalWeight edges

cutScoreBound : (partition : Partition) (edges : List NativeWeightedEdge) ->
  cutScore partition edges ≤ totalWeight edges
cutScoreBound partition [] = ≤-refl
cutScoreBound partition (e ∷ edges) =
  +-mono-≤ (edgeScoreBound partition e) (cutScoreBound partition edges)

checkerCut : Partition
checkerCut = Grid.voxelCheckerColour

xorComplementAlwaysTrue : (b : Bool) ->
  Grid.xorBool (Grid.flipBool b) b ≡ true
xorComplementAlwaysTrue true = refl
xorComplementAlwaysTrue false = refl

checkerCutsEveryNativeEdge :
  ∀ {u v} -> Geometry.HypervoxelAdjacent u v ->
  differentBit (checkerCut u) (checkerCut v) ≡ true
checkerCutsEveryNativeEdge {u} {v} edge
  rewrite Grid.checkerColourFlipsAcrossGrid edge =
    xorComplementAlwaysTrue (checkerCut v)

checkerEdgeScoreFull : (e : NativeWeightedEdge) ->
  edgeScore checkerCut e ≡ weight e
checkerEdgeScoreFull e
  rewrite checkerCutsEveryNativeEdge (adjacent e) = refl

checkerScoreFull : (edges : List NativeWeightedEdge) ->
  cutScore checkerCut edges ≡ totalWeight edges
checkerScoreFull [] = refl
checkerScoreFull (e ∷ edges)
  rewrite checkerEdgeScoreFull e | checkerScoreFull edges = refl

-- Stronger than optimality for uniform weights: any competitor is bounded
-- for each weighted edge, and checkerCut attains EVERY edge.
checkerMaximumCut :
  (edges : List NativeWeightedEdge) ->
  (candidate : Partition) ->
  cutScore candidate edges ≤ cutScore checkerCut edges
checkerMaximumCut edges candidate
  rewrite checkerScoreFull edges = cutScoreBound candidate edges

-- Inverse direction: pull the same selected checkerboard back along the
-- existing pants<->27-grid isomorphism, retaining the typed graph carrier.
pantsCheckerCutsEveryNativeEdge :
  ∀ {p q} -> Grid.Pants3Adjacent p q ->
  differentBit
    (checkerCut (Grid.Pants369.pants3ToVoxel27 p))
    (checkerCut (Grid.Pants369.pants3ToVoxel27 q)) ≡ true
pantsCheckerCutsEveryNativeEdge edge =
  checkerCutsEveryNativeEdge (Grid.pantsToVoxelPreservesAdj edge)

------------------------------------------------------------------------
-- A concrete 54-edge unit-weight witness list, 18 per coordinate axis.
-- All generated edges carry original native adjacency evidence.
-- A complete-enumeration theorem (no missing/duplicate edges) would be
-- additional: this count is specifically for the enumerated list.
------------------------------------------------------------------------

allTrits : List SSP.SSPTrit
allTrits =
  SSP.sspNegOne ∷ SSP.sspZero ∷ SSP.sspPosOne ∷ []

allPairs : List (SSP.SSPTrit × SSP.SSPTrit)
allPairs =
  concatMap
    (λ y -> map (λ z -> y , z) allTrits)
    allTrits

xUnitEdges : SSP.SSPTrit -> SSP.SSPTrit -> List NativeWeightedEdge
xUnitEdges y z =
  native-weighted-edge
    (Geometry.ternary27Point SSP.sspNegOne y z)
    (Geometry.ternary27Point SSP.sspZero y z)
    (Geometry.adjacentX Geometry.negToZero)
    1
  ∷ native-weighted-edge
    (Geometry.ternary27Point SSP.sspZero y z)
    (Geometry.ternary27Point SSP.sspPosOne y z)
    (Geometry.adjacentX Geometry.zeroToPos)
    1
  ∷ []

yUnitEdges : SSP.SSPTrit -> SSP.SSPTrit -> List NativeWeightedEdge
yUnitEdges x z =
  native-weighted-edge
    (Geometry.ternary27Point x SSP.sspNegOne z)
    (Geometry.ternary27Point x SSP.sspZero z)
    (Geometry.adjacentY Geometry.negToZero)
    1
  ∷ native-weighted-edge
    (Geometry.ternary27Point x SSP.sspZero z)
    (Geometry.ternary27Point x SSP.sspPosOne z)
    (Geometry.adjacentY Geometry.zeroToPos)
    1
  ∷ []

zUnitEdges : SSP.SSPTrit -> SSP.SSPTrit -> List NativeWeightedEdge
zUnitEdges x y =
  native-weighted-edge
    (Geometry.ternary27Point x y SSP.sspNegOne)
    (Geometry.ternary27Point x y SSP.sspZero)
    (Geometry.adjacentZ Geometry.negToZero)
    1
  ∷ native-weighted-edge
    (Geometry.ternary27Point x y SSP.sspZero)
    (Geometry.ternary27Point x y SSP.sspPosOne)
    (Geometry.adjacentZ Geometry.zeroToPos)
    1
  ∷ []

unitXWitnesses : List NativeWeightedEdge
unitXWitnesses =
  concatMap (λ pair -> xUnitEdges (proj₁ pair) (proj₂ pair)) allPairs

unitYWitnesses : List NativeWeightedEdge
unitYWitnesses =
  concatMap (λ pair -> yUnitEdges (proj₁ pair) (proj₂ pair)) allPairs

unitZWitnesses : List NativeWeightedEdge
unitZWitnesses =
  concatMap (λ pair -> zUnitEdges (proj₁ pair) (proj₂ pair)) allPairs

unitNativeGridEdges : List NativeWeightedEdge
unitNativeGridEdges =
  unitXWitnesses ++ unitYWitnesses ++ unitZWitnesses

unitWitnessCountIs54 : length unitNativeGridEdges ≡ 54
unitWitnessCountIs54 = refl

unitWitnessTotalWeightIs54 : totalWeight unitNativeGridEdges ≡ 54
unitWitnessTotalWeightIs54 = refl

checkerWitnessScoreIs54 : cutScore checkerCut unitNativeGridEdges ≡ 54
checkerWitnessScoreIs54 =
  trans (checkerScoreFull unitNativeGridEdges) unitWitnessTotalWeightIs54

maxCutFor54WitnessedEdges :
  (candidate : Partition) ->
  cutScore candidate unitNativeGridEdges ≤ 54
maxCutFor54WitnessedEdges candidate =
  subst
    (λ sum -> cutScore candidate unitNativeGridEdges ≤ sum)
    unitWitnessTotalWeightIs54
    (cutScoreBound candidate unitNativeGridEdges)

record NativeGridMaxCutBoundary : Set where
  constructor native-grid-max-cut-boundary
  field
    nativeAdjacencyReused : Bool
    selectedCutSaturatesEveryNativeEdge : Bool
    finiteNonnegativeWeightedOptimality : Bool
    fiftyFourConcreteUnitEdgeWitnesses : Bool
    fullGraphEdgeEnumerationUniquenessKernelChecked : Bool
    arbitraryDirectedWeightedGraphBipartite : Bool
    QidOrPaperCreatesThisProof : Bool
    AgdaExactHeadChecked : Bool

canonicalNativeGridMaxCutBoundary : NativeGridMaxCutBoundary
canonicalNativeGridMaxCutBoundary =
  native-grid-max-cut-boundary
    true true true true false false false false
