module DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Enumerate the complete second derivative of one ordered four-link Wilson
-- plaquette product.  There are exactly
--
--   4 diagonal placements of a second link derivative
--     + 12 ordered placements of two first link derivatives
--     = 16 ordered second-variation atoms.
--
-- The twelve cross placements are also proved to be the concatenation of six
-- unordered slot pairs, each carrying its two derivative orders.  This is the
-- finite combinatorial carrier needed before identifying each atom with its
-- transported/factorised quaternion operator term.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data PlaquetteLinkSlot4 : Set where
  slot0 slot1 slot2 slot3 : PlaquetteLinkSlot4

plaquetteLinkSlots4 : List PlaquetteLinkSlot4
plaquetteLinkSlots4 = slot0 ∷ slot1 ∷ slot2 ∷ slot3 ∷ []

data UnorderedSlotPair4 : Set where
  pair01 pair02 pair03 pair12 pair13 pair23 : UnorderedSlotPair4

unorderedSlotPairs4 : List UnorderedSlotPair4
unorderedSlotPairs4 =
  pair01 ∷ pair02 ∷ pair03 ∷ pair12 ∷ pair13 ∷ pair23 ∷ []

data OrderedDistinctSlotPair4 : Set where
  ordered01 ordered10 ordered02 ordered20 ordered03 ordered30 :
    OrderedDistinctSlotPair4
  ordered12 ordered21 ordered13 ordered31 ordered23 ordered32 :
    OrderedDistinctSlotPair4

orderedDistinctSlotPairs4 : List OrderedDistinctSlotPair4
orderedDistinctSlotPairs4 =
  ordered01 ∷ ordered10 ∷ ordered02 ∷ ordered20 ∷
  ordered03 ∷ ordered30 ∷ ordered12 ∷ ordered21 ∷
  ordered13 ∷ ordered31 ∷ ordered23 ∷ ordered32 ∷ []

orderedPairFirst : OrderedDistinctSlotPair4 → PlaquetteLinkSlot4
orderedPairFirst ordered01 = slot0
orderedPairFirst ordered10 = slot1
orderedPairFirst ordered02 = slot0
orderedPairFirst ordered20 = slot2
orderedPairFirst ordered03 = slot0
orderedPairFirst ordered30 = slot3
orderedPairFirst ordered12 = slot1
orderedPairFirst ordered21 = slot2
orderedPairFirst ordered13 = slot1
orderedPairFirst ordered31 = slot3
orderedPairFirst ordered23 = slot2
orderedPairFirst ordered32 = slot3

orderedPairSecond : OrderedDistinctSlotPair4 → PlaquetteLinkSlot4
orderedPairSecond ordered01 = slot1
orderedPairSecond ordered10 = slot0
orderedPairSecond ordered02 = slot2
orderedPairSecond ordered20 = slot0
orderedPairSecond ordered03 = slot3
orderedPairSecond ordered30 = slot0
orderedPairSecond ordered12 = slot2
orderedPairSecond ordered21 = slot1
orderedPairSecond ordered13 = slot3
orderedPairSecond ordered31 = slot1
orderedPairSecond ordered23 = slot3
orderedPairSecond ordered32 = slot2

orderedPairReverse : OrderedDistinctSlotPair4 → OrderedDistinctSlotPair4
orderedPairReverse ordered01 = ordered10
orderedPairReverse ordered10 = ordered01
orderedPairReverse ordered02 = ordered20
orderedPairReverse ordered20 = ordered02
orderedPairReverse ordered03 = ordered30
orderedPairReverse ordered30 = ordered03
orderedPairReverse ordered12 = ordered21
orderedPairReverse ordered21 = ordered12
orderedPairReverse ordered13 = ordered31
orderedPairReverse ordered31 = ordered13
orderedPairReverse ordered23 = ordered32
orderedPairReverse ordered32 = ordered23

orderedPairReverseInvolutive : ∀ pair →
  orderedPairReverse (orderedPairReverse pair) ≡ pair
orderedPairReverseInvolutive ordered01 = refl
orderedPairReverseInvolutive ordered10 = refl
orderedPairReverseInvolutive ordered02 = refl
orderedPairReverseInvolutive ordered20 = refl
orderedPairReverseInvolutive ordered03 = refl
orderedPairReverseInvolutive ordered30 = refl
orderedPairReverseInvolutive ordered12 = refl
orderedPairReverseInvolutive ordered21 = refl
orderedPairReverseInvolutive ordered13 = refl
orderedPairReverseInvolutive ordered31 = refl
orderedPairReverseInvolutive ordered23 = refl
orderedPairReverseInvolutive ordered32 = refl

orderedPairForUnordered :
  UnorderedSlotPair4 → List OrderedDistinctSlotPair4
orderedPairForUnordered pair01 = ordered01 ∷ ordered10 ∷ []
orderedPairForUnordered pair02 = ordered02 ∷ ordered20 ∷ []
orderedPairForUnordered pair03 = ordered03 ∷ ordered30 ∷ []
orderedPairForUnordered pair12 = ordered12 ∷ ordered21 ∷ []
orderedPairForUnordered pair13 = ordered13 ∷ ordered31 ∷ []
orderedPairForUnordered pair23 = ordered23 ∷ ordered32 ∷ []

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (value ∷ values) right = value ∷ append values right

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap function [] = []
concatMap function (value ∷ values) =
  append (function value) (concatMap function values)

orderedPairsAreSixTwoOrientationFibres :
  orderedDistinctSlotPairs4
  ≡ concatMap orderedPairForUnordered unorderedSlotPairs4
orderedPairsAreSixTwoOrientationFibres = refl

data PlaquetteSecondVariationPlacement4 : Set where
  secondAt0 secondAt1 secondAt2 secondAt3 :
    PlaquetteSecondVariationPlacement4
  firstFirst : OrderedDistinctSlotPair4 →
    PlaquetteSecondVariationPlacement4

plaquetteSecondVariationPlacements4 :
  List PlaquetteSecondVariationPlacement4
plaquetteSecondVariationPlacements4 =
  secondAt0 ∷ secondAt1 ∷ secondAt2 ∷ secondAt3 ∷
  firstFirst ordered01 ∷ firstFirst ordered10 ∷
  firstFirst ordered02 ∷ firstFirst ordered20 ∷
  firstFirst ordered03 ∷ firstFirst ordered30 ∷
  firstFirst ordered12 ∷ firstFirst ordered21 ∷
  firstFirst ordered13 ∷ firstFirst ordered31 ∷
  firstFirst ordered23 ∷ firstFirst ordered32 ∷ []

diagonalPlacementCountExact : length plaquetteLinkSlots4 ≡ 4
diagonalPlacementCountExact = refl

unorderedCrossPairCountExact : length unorderedSlotPairs4 ≡ 6
unorderedCrossPairCountExact = refl

orderedCrossPlacementCountExact : length orderedDistinctSlotPairs4 ≡ 12
orderedCrossPlacementCountExact = refl

plaquetteSecondVariationPlacementCountExact :
  length plaquetteSecondVariationPlacements4 ≡ 16
plaquetteSecondVariationPlacementCountExact = refl

wilsonPlaquetteSecondVariationPlacementLevel : ProofLevel
wilsonPlaquetteSecondVariationPlacementLevel = machineChecked

wilsonPlaquetteCrossOrientationFibreLevel : ProofLevel
wilsonPlaquetteCrossOrientationFibreLevel = machineChecked
