module DASHI.Core.RelationalHypervoxelBraidCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set; Set₁)

------------------------------------------------------------------------
-- Hypervoxel / braid / ultrametric locality core.
--
-- A local cell indexes body, time, place, relation, affect, story, conduct,
-- and flow without collapsing those strands.  The ultrametric lane records
-- shared-root proximity separately from linear/surface proximity.

record RelationalHypervoxel : Set₁ where
  field
    Body : Set
    Time : Set
    Place : Set
    Relation : Set
    Affect : Set
    Story : Set
    Conduct : Set
    Flow : Set

record HypervoxelPoint (H : RelationalHypervoxel) : Set where
  field
    body : RelationalHypervoxel.Body H
    time : RelationalHypervoxel.Time H
    place : RelationalHypervoxel.Place H
    relation : RelationalHypervoxel.Relation H
    affect : RelationalHypervoxel.Affect H
    story : RelationalHypervoxel.Story H
    conduct : RelationalHypervoxel.Conduct H
    flow : RelationalHypervoxel.Flow H

record BraidPreservation (H : RelationalHypervoxel) : Set₁ where
  field
    BodyStrand : Set
    PlaceStrand : Set
    StoryStrand : Set
    RelationStrand : Set

    bodyStrandNotCollapsedToPlace : Bool
    bodyStrandNotCollapsedToPlaceIsFalse :
      bodyStrandNotCollapsedToPlace ≡ false

    storyStrandNotCollapsedToBiology : Bool
    storyStrandNotCollapsedToBiologyIsFalse :
      storyStrandNotCollapsedToBiology ≡ false

record DualDistanceSurface : Set₁ where
  field
    Point : Set
    LinearDistance : Point → Point → Set
    SharedRootDistance : Point → Point → Set

    surfaceFarRootNear : Point → Point → Set

record UltrametricReactivationWitness
  (D : DualDistanceSurface) (x event : DualDistanceSurface.Point D) : Set where
  field
    farOnSurfaceNearAtRoot :
      DualDistanceSurface.surfaceFarRootNear D x event

------------------------------------------------------------------------
-- Governance boundary.

record HypervoxelGovernance : Set where
  constructor mkHypervoxelGovernance
  field
    localCellIsWholePerson : Bool
    localCellIsWholePersonIsFalse : localCellIsWholePerson ≡ false

    sharedRootSimilarityIsRecoveredMemory : Bool
    sharedRootSimilarityIsRecoveredMemoryIsFalse :
      sharedRootSimilarityIsRecoveredMemory ≡ false

    braidCollapsesStrands : Bool
    braidCollapsesStrandsIsFalse : braidCollapsesStrands ≡ false

canonicalHypervoxelGovernance : HypervoxelGovernance
canonicalHypervoxelGovernance =
  mkHypervoxelGovernance false refl false refl false refl
