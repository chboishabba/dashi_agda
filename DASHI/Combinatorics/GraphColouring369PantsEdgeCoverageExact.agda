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


------------------------------------------------------------------------
-- Explicit propositional NODUP for the 54 canonical slots.
--
-- A decidable syntactic slot-comparison function is used only to
-- construct a proof of non-duplication for the closed enumerated list.
-- It is NOT presumed to identify two distinct native graph owners.
------------------------------------------------------------------------

andBit : Bool -> Bool -> Bool
andBit true b = b
andBit false _ = false

notBit : Bool -> Bool
notBit true = false
notBit false = true

sameTrit : SSP.SSPTrit -> SSP.SSPTrit -> Bool
sameTrit SSP.sspNegOne SSP.sspNegOne = true
sameTrit SSP.sspNegOne SSP.sspZero = false
sameTrit SSP.sspNegOne SSP.sspPosOne = false
sameTrit SSP.sspZero SSP.sspNegOne = false
sameTrit SSP.sspZero SSP.sspZero = true
sameTrit SSP.sspZero SSP.sspPosOne = false
sameTrit SSP.sspPosOne SSP.sspNegOne = false
sameTrit SSP.sspPosOne SSP.sspZero = false
sameTrit SSP.sspPosOne SSP.sspPosOne = true

sameTritRefl : (x : SSP.SSPTrit) -> sameTrit x x ≡ true
sameTritRefl SSP.sspNegOne = refl
sameTritRefl SSP.sspZero = refl
sameTritRefl SSP.sspPosOne = refl

sameStep : PositiveStep -> PositiveStep -> Bool
sameStep lowerStep lowerStep = true
sameStep lowerStep upperStep = false
sameStep upperStep lowerStep = false
sameStep upperStep upperStep = true

sameStepRefl : (x : PositiveStep) -> sameStep x x ≡ true
sameStepRefl lowerStep = refl
sameStepRefl upperStep = refl

threeBits : Bool -> Bool -> Bool -> Bool
threeBits a b c = andBit a (andBit b c)

sameSlot : NativeEdgeSlot -> NativeEdgeSlot -> Bool
sameSlot (slotX a b s) (slotX c d t) =
  threeBits (sameTrit a c) (sameTrit b d) (sameStep s t)
sameSlot (slotX a b s) (slotY c d t) = false
sameSlot (slotX a b s) (slotZ c d t) = false
sameSlot (slotY a b s) (slotX c d t) = false
sameSlot (slotY a b s) (slotY c d t) =
  threeBits (sameTrit a c) (sameTrit b d) (sameStep s t)
sameSlot (slotY a b s) (slotZ c d t) = false
sameSlot (slotZ a b s) (slotX c d t) = false
sameSlot (slotZ a b s) (slotY c d t) = false
sameSlot (slotZ a b s) (slotZ c d t) =
  threeBits (sameTrit a c) (sameTrit b d) (sameStep s t)

sameSlotRefl : (slot : NativeEdgeSlot) -> sameSlot slot slot ≡ true
sameSlotRefl (slotX a b s)
  rewrite sameTritRefl a | sameTritRefl b | sameStepRefl s = refl
sameSlotRefl (slotY a b s)
  rewrite sameTritRefl a | sameTritRefl b | sameStepRefl s = refl
sameSlotRefl (slotZ a b s)
  rewrite sameTritRefl a | sameTritRefl b | sameStepRefl s = refl

andLeftTrue : (a b : Bool) -> andBit a b ≡ true -> a ≡ true
andLeftTrue true b _ = refl
andLeftTrue false b ()

andRightTrue : (a b : Bool) -> andBit a b ≡ true -> b ≡ true
andRightTrue true b eq = eq
andRightTrue false b ()

falseIsNotTrue : false ≡ true -> ⊥
falseIsNotTrue ()

slotNotEqualWhenComparisonFalse :
  (a b : NativeEdgeSlot) ->
  notBit (sameSlot a b) ≡ true ->
  a ≡ b -> ⊥
slotNotEqualWhenComparisonFalse a .a comparison refl =
  falseIsNotTrue
    (trans
      (sym (cong notBit (sameSlotRefl a)))
      comparison)

noSlotMatch : NativeEdgeSlot -> List NativeEdgeSlot -> Bool
noSlotMatch x [] = true
noSlotMatch x (y ∷ ys) =
  andBit (notBit (sameSlot x y)) (noSlotMatch x ys)

data SlotMember (item : NativeEdgeSlot) : List NativeEdgeSlot -> Set where
  memberHead : ∀ {rest} -> SlotMember item (item ∷ rest)
  memberTail : ∀ {x rest} ->
    SlotMember item rest -> SlotMember item (x ∷ rest)

noSlotMatchExcludes :
  (x : NativeEdgeSlot) (xs : List NativeEdgeSlot) ->
  noSlotMatch x xs ≡ true ->
  ∀ {y} -> SlotMember y xs -> x ≡ y -> ⊥
noSlotMatchExcludes x [] _ ()
noSlotMatchExcludes x (y ∷ ys) noMatch memberHead equality =
  slotNotEqualWhenComparisonFalse x y
    (andLeftTrue (notBit (sameSlot x y))
      (noSlotMatch x ys) noMatch)
    equality
noSlotMatchExcludes x (y ∷ ys) noMatch (memberTail membership) equality =
  noSlotMatchExcludes x ys
    (andRightTrue (notBit (sameSlot x y))
      (noSlotMatch x ys) noMatch)
    membership equality

noDuplicateSlotsBit : List NativeEdgeSlot -> Bool
noDuplicateSlotsBit [] = true
noDuplicateSlotsBit (x ∷ xs) =
  andBit (noSlotMatch x xs) (noDuplicateSlotsBit xs)

data NoDuplicateSlots : List NativeEdgeSlot -> Set where
  emptyDistinct : NoDuplicateSlots []
  prependDistinct : ∀ {x xs} ->
    (∀ {y} -> SlotMember y xs -> x ≡ y -> ⊥) ->
    NoDuplicateSlots xs -> NoDuplicateSlots (x ∷ xs)

noDuplicateSlotsSound :
  (xs : List NativeEdgeSlot) ->
  noDuplicateSlotsBit xs ≡ true ->
  NoDuplicateSlots xs
noDuplicateSlotsSound [] _ = emptyDistinct
noDuplicateSlotsSound (x ∷ xs) ok =
  prependDistinct
    (noSlotMatchExcludes x xs
      (andLeftTrue (noSlotMatch x xs)
        (noDuplicateSlotsBit xs) ok))
    (noDuplicateSlotsSound xs
      (andRightTrue (noSlotMatch x xs)
        (noDuplicateSlotsBit xs) ok))

closedFiftyFourSlotsDistinctBit :
  noDuplicateSlotsBit allNativeSlots ≡ true
closedFiftyFourSlotsDistinctBit = refl

-- This is a genuine propositional absence-of-duplicate-slot witness,
-- conditional only on the exact-head Agda typechecker accepting the file.
allFiftyFourSlotsPairwiseDistinct : NoDuplicateSlots allNativeSlots
allFiftyFourSlotsPairwiseDistinct =
  noDuplicateSlotsSound allNativeSlots closedFiftyFourSlotsDistinctBit

record EdgeChartCoverageBoundary : Set where
  constructor edge-chart-coverage-boundary
  field
    everyActualNativeAdjacencyHasChart : Bool
    actualConstructorsExhausted : Bool
    exact54CanonicalSlots : Bool
    exactExistingEdgeListRoundTrip : Bool
    exactZeroToFiftyThreeIdentifierCensus : Bool
    typedClosedListNoDuplicatesWritten : Bool
    slotIdInjectivityEstablishedHere : Bool
    exactHeadAgdaKernelChecked : Bool
    smoothOrPhysicalPantsClaimed : Bool

canonicalEdgeChartCoverageBoundary : EdgeChartCoverageBoundary
canonicalEdgeChartCoverageBoundary =
  edge-chart-coverage-boundary true true true true true true false false false
