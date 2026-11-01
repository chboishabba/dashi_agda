module DASHI.Biology.ReasoningFieldRenderBridgeExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Biology.PadicCylinderLODReasoningField as LOD

------------------------------------------------------------------------
-- The exact reasoning state remains an address plus field mass.  Rendering is
-- a typed observation channel carrying the source address as metadata.  Camera
-- projection and colour/opacity composition are intentionally non-injective.

record ReasoningCell : Set where
  constructor reasoningCell
  field
    sourceAddress : LOD.DepthSixAddress
    sourceField : LOD.NodeField

open ReasoningCell public

record RenderSample : Set where
  constructor renderSample
  field
    renderVoxel : LOD.Voxel3
    redChannel : Nat
    greenChannel : Nat
    blueChannel : Nat
    opacityChannel : Nat
    retainedAddress : LOD.DepthSixAddress

open RenderSample public

renderReasoningCell : ReasoningCell → RenderSample
renderReasoningCell cell =
  renderSample
    (LOD.flattenHierarchicalVoxel (LOD.embedDepthSix (sourceAddress cell)))
    (LOD.class9Mass (sourceField cell))
    (LOD.class6Mass (sourceField cell))
    (LOD.class3Mass (sourceField cell))
    (LOD.totalMass (sourceField cell))
    (sourceAddress cell)

canonicalReasoningCell : ReasoningCell
canonicalReasoningCell =
  reasoningCell
    LOD.sampleDepthSix
    LOD.canonicalCoarseField

renderRetainsExactAddress :
  retainedAddress (renderReasoningCell canonicalReasoningCell)
  ≡
  sourceAddress canonicalReasoningCell
renderRetainsExactAddress = refl

canonicalRenderVoxel :
  renderVoxel (renderReasoningCell canonicalReasoningCell)
  ≡
  LOD.voxel3 5 7 0
canonicalRenderVoxel = refl

canonicalRenderChannels :
  redChannel (renderReasoningCell canonicalReasoningCell) ≡ 4
  ×
  greenChannel (renderReasoningCell canonicalReasoningCell) ≡ 3
  ×
  blueChannel (renderReasoningCell canonicalReasoningCell) ≡ 2
  ×
  opacityChannel (renderReasoningCell canonicalReasoningCell) ≡ 9
canonicalRenderChannels = refl , (refl , (refl , refl))

------------------------------------------------------------------------
-- Shared coarse prefixes permit exact cache reuse even when fine voxels differ.

sameCoarseAddressA : LOD.DepthSixAddress
sameCoarseAddressA =
  U369.digit3 vcons U369.digit6 vcons U369.digit9 vcons
  U369.digit3 vcons U369.digit3 vcons U369.digit3 vcons vnil

sameCoarseAddressB : LOD.DepthSixAddress
sameCoarseAddressB =
  U369.digit3 vcons U369.digit6 vcons U369.digit9 vcons
  U369.digit9 vcons U369.digit9 vcons U369.digit9 vcons vnil

coarseVoxelCacheKeyAgrees :
  LOD.coarseVoxel (LOD.embedDepthSix sameCoarseAddressA)
  ≡
  LOD.coarseVoxel (LOD.embedDepthSix sameCoarseAddressB)
coarseVoxelCacheKeyAgrees = refl

fineVoxelStillDiffers :
  LOD.fineVoxel (LOD.embedDepthSix sameCoarseAddressA)
  ≡
  LOD.voxel3 0 0 0
  ×
  LOD.fineVoxel (LOD.embedDepthSix sameCoarseAddressB)
  ≡
  LOD.voxel3 2 2 2
fineVoxelStillDiffers = refl , refl

------------------------------------------------------------------------
-- Inverse-density display is an observation polarity, not negative source mass.

inverseIntensity : Nat → Nat → Nat
inverseIntensity calibration mass = calibration ∸ mass

higherMassAppearsDarkerInCanonicalPair :
  inverseIntensity 9 7 ≡ 2
  ×
  inverseIntensity 9 3 ≡ 6
higherMassAppearsDarkerInCanonicalPair = refl , refl

------------------------------------------------------------------------
-- A deliberately simple camera projection supplies an exact non-injectivity
-- witness.  The voxel image cannot replace the retained source address.

record ScreenPixel : Set where
  constructor screenPixel
  field
    screenU : Nat
    screenV : Nat

open ScreenPixel public

cameraProject : LOD.Voxel3 → ScreenPixel
cameraProject voxel =
  screenPixel
    (LOD.voxelX voxel + LOD.voxelZ voxel)
    (LOD.voxelY voxel)

voxelA : LOD.Voxel3
voxelA = LOD.voxel3 1 2 1

voxelB : LOD.Voxel3
voxelB = LOD.voxel3 2 2 0

cameraProjectionCollision :
  cameraProject voxelA ≡ cameraProject voxelB
cameraProjectionCollision = refl

record ReasoningFieldRenderBoundary : Set where
  constructor reasoningFieldRenderBoundary
  field
    finalImageIsPrimaryState : Bool
    finalImageIsPrimaryStateIsFalse : finalImageIsPrimaryState ≡ false

    renderProjectionIsInjective : Bool
    renderProjectionIsInjectiveIsFalse : renderProjectionIsInjective ≡ false

    inverseViewUsesNegativeEventMass : Bool
    inverseViewUsesNegativeEventMassIsFalse :
      inverseViewUsesNegativeEventMass ≡ false

    addressMetadataMustBeRetained : Bool
    addressMetadataMustBeRetainedIsTrue :
      addressMetadataMustBeRetained ≡ true

open ReasoningFieldRenderBoundary public

canonicalReasoningFieldRenderBoundary : ReasoningFieldRenderBoundary
canonicalReasoningFieldRenderBoundary =
  reasoningFieldRenderBoundary false refl false refl false refl true refl
