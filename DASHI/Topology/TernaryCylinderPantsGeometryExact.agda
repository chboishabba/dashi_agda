module DASHI.Topology.TernaryCylinderPantsGeometryExact where

------------------------------------------------------------------------
-- TERNARY CYLINDER <-> 1-TO-3 PANTS BRIDGE
--
-- Legacy motivation:
--   dashifine/43_viz_ultrametric_tree.py
--   dashifine/45_viz_tree_density.py
--   dashifine README pants_* gallery artifacts
--
-- Existing theorem-bearing inputs:
--   * SSP369Ultrametric: ternary finite-prefix addresses and ultrametric law;
--   * PadicCylinderLODReasoningField: exact cylinder refinement and 3D voxel
--     observation layout;
--   * RelationalBranchCobordismGeometry: exact composable 1 -> n pants carrier.
--
-- Source vocabulary boundary:
--   Michael F. Atiyah, "Topological quantum field theory",
--   Publications Mathematiques de l'IHES 68 (1988), 175-186,
--   DOI 10.1007/BF02698547.
--
-- Atiyah supplies boundary/gluing/cobordism vocabulary only.  This file proves
-- a finite combinatorial correspondence.  It does not claim a smooth surface,
-- a TQFT, or identity between a totally disconnected p-adic fibre and a
-- connected Euclidean pair-of-pants surface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Biology.PadicCylinderLODReasoningField as Padic
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants

------------------------------------------------------------------------
-- Generic radix-3 refinement at arbitrary finite address depth.
------------------------------------------------------------------------

appendDigit :
  ∀ {n : Nat} → U369.Address n → U369.Digit369 → U369.Address (suc n)
appendDigit vnil digit = digit vcons vnil
appendDigit (head vcons tail) digit = head vcons appendDigit tail digit

-- All three children of a depth-n address share the complete depth-n parent
-- prefix.  This is the intrinsic cylinder/tree statement independent of any
-- Euclidean visualization.
refinedSiblingsShareParentPrefix :
  ∀ {n : Nat}
    (parent : U369.Address n)
    (left right : U369.Digit369) →
  U369.PrefixMatch n
    (appendDigit parent left)
    (appendDigit parent right)
refinedSiblingsShareParentPrefix vnil left right = U369.prefix-zero
refinedSiblingsShareParentPrefix (head vcons tail) left right =
  U369.prefix-cons head
    (refinedSiblingsShareParentPrefix tail left right)

child3 child6 child9 :
  ∀ {n : Nat} → U369.Address n → U369.Address (suc n)
child3 parent = appendDigit parent U369.digit3
child6 parent = appendDigit parent U369.digit6
child9 parent = appendDigit parent U369.digit9

child3Child6ShareParentPrefix :
  ∀ {n : Nat} (parent : U369.Address n) →
  U369.PrefixMatch n (child3 parent) (child6 parent)
child3Child6ShareParentPrefix parent =
  refinedSiblingsShareParentPrefix parent U369.digit3 U369.digit6

child3Child9ShareParentPrefix :
  ∀ {n : Nat} (parent : U369.Address n) →
  U369.PrefixMatch n (child3 parent) (child9 parent)
child3Child9ShareParentPrefix parent =
  refinedSiblingsShareParentPrefix parent U369.digit3 U369.digit9

child6Child9ShareParentPrefix :
  ∀ {n : Nat} (parent : U369.Address n) →
  U369.PrefixMatch n (child6 parent) (child9 parent)
child6Child9ShareParentPrefix parent =
  refinedSiblingsShareParentPrefix parent U369.digit6 U369.digit9

------------------------------------------------------------------------
-- Exact three-slot indexing of the existing composed 1 -> 3 pants object.
------------------------------------------------------------------------

data BranchSlot : Set where
  slot3 slot6 slot9 : BranchSlot

slotOfDigit : U369.Digit369 → BranchSlot
slotOfDigit U369.digit3 = slot3
slotOfDigit U369.digit6 = slot6
slotOfDigit U369.digit9 = slot9

digitOfSlot : BranchSlot → U369.Digit369
digitOfSlot slot3 = U369.digit3
digitOfSlot slot6 = U369.digit6
digitOfSlot slot9 = U369.digit9

digitSlotRoundTrip :
  (digit : U369.Digit369) → digitOfSlot (slotOfDigit digit) ≡ digit
digitSlotRoundTrip U369.digit3 = refl
digitSlotRoundTrip U369.digit6 = refl
digitSlotRoundTrip U369.digit9 = refl

slotDigitRoundTrip :
  (slot : BranchSlot) → slotOfDigit (digitOfSlot slot) ≡ slot
slotDigitRoundTrip slot3 = refl
slotDigitRoundTrip slot6 = refl
slotDigitRoundTrip slot9 = refl

channelOfSlot : BranchSlot → Pants.BranchChannel
channelOfSlot slot3 = Pants.fineChannelA
channelOfSlot slot6 = Pants.fineChannelB
channelOfSlot slot9 = Pants.remainderChannel1

channelOfDigit : U369.Digit369 → Pants.BranchChannel
channelOfDigit digit = channelOfSlot (slotOfDigit digit)

-- The existing exact composition of two 1 -> 2 pants has exactly these three
-- unit output channels, in the same order as the ternary digit slots.
canonicalPantsOutputsMatchTernarySlots :
  Pants.fineOutputs Pants.composedOneToThree
  ≡ channelOfSlot slot3 ∷ channelOfSlot slot6 ∷ channelOfSlot slot9 ∷ []
canonicalPantsOutputsMatchTernarySlots = refl

canonicalPantsHasThreeOutputs : Pants.outputCount Pants.composedOneToThree ≡ 3
canonicalPantsHasThreeOutputs = Pants.composedOutputCountIsThree

canonicalPantsCapacityConservative :
  Pants.CapacityConservative Pants.composedOneToThree
canonicalPantsCapacityConservative = Pants.composedCapacityConservative

canonicalPantsWaveConservative :
  Pants.WaveConservative Pants.composedOneToThree
canonicalPantsWaveConservative = Pants.composedWaveConservative

------------------------------------------------------------------------
-- Cylinder/pants commuting interface.
------------------------------------------------------------------------

record CylinderPantsBridge {n : Nat} (parent : U369.Address n) : Set where
  constructor cylinderPantsBridge
  field
    refinedChild : U369.Digit369 → U369.Address (suc n)
    outputSlot : U369.Digit369 → BranchSlot
    outputChannel : U369.Digit369 → Pants.BranchChannel

    childIsExactRefinement :
      (digit : U369.Digit369) →
      refinedChild digit ≡ appendDigit parent digit

    slotMatchesDigit :
      (digit : U369.Digit369) →
      outputSlot digit ≡ slotOfDigit digit

    channelMatchesSlot :
      (digit : U369.Digit369) →
      outputChannel digit ≡ channelOfSlot (outputSlot digit)

open CylinderPantsBridge public

canonicalCylinderPantsBridge :
  ∀ {n : Nat} (parent : U369.Address n) → CylinderPantsBridge parent
canonicalCylinderPantsBridge parent =
  cylinderPantsBridge
    (appendDigit parent)
    slotOfDigit
    channelOfDigit
    (λ digit → refl)
    (λ digit → refl)
    (λ digit → refl)

-- At the depth-one cylinder layer this bridge commutes with the repository's
-- existing exact prefix/refinement map: geometrically choosing one of the three
-- pants outputs corresponds to choosing one of the three refined cylinders,
-- and forgetting that choice recovers the same parent cylinder.
depthOneCylinderRefinementReturnsParent :
  (parent : Padic.DepthOneAddress) (digit : U369.Digit369) →
  Padic.prefixTwoToOne (Padic.refineOne parent digit) ≡ parent
depthOneCylinderRefinementReturnsParent = Padic.prefixRefinementReturnsParent

------------------------------------------------------------------------
-- Concrete depth-three 3D observation of one ternary parent and its children.
--
-- This is deliberately extrinsic.  The voxel layout is an observation map,
-- not an isometric realization of the p-adic/ultrametric geometry.
------------------------------------------------------------------------

sampleDepthTwoParent : U369.Address 2
sampleDepthTwoParent = U369.digit3 vcons U369.digit6 vcons vnil

sampleChild3 sampleChild6 sampleChild9 : Padic.DepthThreeAddress
sampleChild3 = child3 sampleDepthTwoParent
sampleChild6 = child6 sampleDepthTwoParent
sampleChild9 = child9 sampleDepthTwoParent

sampleChild3Voxel :
  Padic.embedDepthThree sampleChild3 ≡ Padic.voxel3 0 1 0
sampleChild3Voxel = refl

sampleChild6Voxel :
  Padic.embedDepthThree sampleChild6 ≡ Padic.voxel3 0 1 1
sampleChild6Voxel = refl

sampleChild9Voxel :
  Padic.embedDepthThree sampleChild9 ≡ Padic.voxel3 0 1 2
sampleChild9Voxel = refl

sampleChildrenShareDepthTwoCylinder36 :
  U369.PrefixMatch 2 sampleChild3 sampleChild6
sampleChildrenShareDepthTwoCylinder36 =
  child3Child6ShareParentPrefix sampleDepthTwoParent

sampleChildrenShareDepthTwoCylinder39 :
  U369.PrefixMatch 2 sampleChild3 sampleChild9
sampleChildrenShareDepthTwoCylinder39 =
  child3Child9ShareParentPrefix sampleDepthTwoParent

sampleChildrenShareDepthTwoCylinder69 :
  U369.PrefixMatch 2 sampleChild6 sampleChild9
sampleChildrenShareDepthTwoCylinder69 =
  child6Child9ShareParentPrefix sampleDepthTwoParent

------------------------------------------------------------------------
-- Promotion boundary for the eventual continuous 3D thickening theorem.
------------------------------------------------------------------------

record TernaryPantsGeometryBoundary : Set where
  constructor ternaryPantsGeometryBoundary
  field
    ternaryCylinderTreeFormalized : Bool
    ternaryCylinderTreeFormalizedIsTrue : ternaryCylinderTreeFormalized ≡ true

    cylinderToPantsSlotCorrespondenceFormalized : Bool
    cylinderToPantsSlotCorrespondenceFormalizedIsTrue :
      cylinderToPantsSlotCorrespondenceFormalized ≡ true

    voxelObservationAvailable : Bool
    voxelObservationAvailableIsTrue : voxelObservationAvailable ≡ true

    voxelEmbeddingIsUltrametricIsometry : Bool
    voxelEmbeddingIsUltrametricIsometryIsFalse :
      voxelEmbeddingIsUltrametricIsometry ≡ false

    padicFibreIsConnectedPantsSurface : Bool
    padicFibreIsConnectedPantsSurfaceIsFalse :
      padicFibreIsConnectedPantsSurface ≡ false

    smoothEmbeddedPantsThickeningConstructed : Bool
    smoothEmbeddedPantsThickeningConstructedIsFalse :
      smoothEmbeddedPantsThickeningConstructed ≡ false

open TernaryPantsGeometryBoundary public

canonicalTernaryPantsGeometryBoundary : TernaryPantsGeometryBoundary
canonicalTernaryPantsGeometryBoundary =
  ternaryPantsGeometryBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
