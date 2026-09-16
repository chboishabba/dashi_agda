module DASHI.ComputerScience.RSA260BidiFactorLayerStructureCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact as Codec
import DASHI.ComputerScience.RSA260BidiGF2FactorMaskDecoderExact as Decoder
import DASHI.ComputerScience.RSA260BidiGF2FactorPacketFullPortfolioExact as Full
import DASHI.ComputerScience.RSA260BidiHybridTailCostShapeCollisionExact as Cost

------------------------------------------------------------------------
-- FACTOR-LAYER STRUCTURE COLLISION
--
-- The previous attack showed rotate3 and affine7 share the complete recorded
-- codec cost shape.  Descend again into the hybrid tail rather than appending
-- another scalar.  The compiled factor-mode portfolio shows that these two
-- generators have the same factor-mode footprint (layers 0,1,16), and at each
-- of those layers the selected GF(2) basis and every row-coordinate mask are
-- definitionally identical.
--
-- Yet their recovered generator identities differ.  Therefore low-rank/factor
-- structure itself is still not the exact-generator consumer terminal.  On
-- this witness, the discriminating information lies in the complementary raw
-- layer payload retained by the hybrid representation.
------------------------------------------------------------------------

record FactorLayer : Set where
  constructor factor-layer
  field
    basis : Decoder.FactorBasis8
    mask0 mask1 mask2 mask3 mask4 mask5 mask6 mask7 : Decoder.FactorMask8
open FactorLayer public

record FactorFootprint : Set where
  constructor factor-footprint
  field
    firstLayer secondLayer thirdLayer : Nat
open FactorFootprint public

record FactorLayerStructure : Set where
  constructor factor-layer-structure
  field
    footprint : FactorFootprint
    first second third : FactorLayer
open FactorLayerStructure public

mkRotate3Layer0 : FactorLayer
mkRotate3Layer0 = factor-layer
  Full.rotate3Layer0Basis
  Full.rotate3Layer0Row0Mask Full.rotate3Layer0Row1Mask
  Full.rotate3Layer0Row2Mask Full.rotate3Layer0Row3Mask
  Full.rotate3Layer0Row4Mask Full.rotate3Layer0Row5Mask
  Full.rotate3Layer0Row6Mask Full.rotate3Layer0Row7Mask

mkRotate3Layer1 : FactorLayer
mkRotate3Layer1 = factor-layer
  Full.rotate3Layer1Basis
  Full.rotate3Layer1Row0Mask Full.rotate3Layer1Row1Mask
  Full.rotate3Layer1Row2Mask Full.rotate3Layer1Row3Mask
  Full.rotate3Layer1Row4Mask Full.rotate3Layer1Row5Mask
  Full.rotate3Layer1Row6Mask Full.rotate3Layer1Row7Mask

mkRotate3Layer16 : FactorLayer
mkRotate3Layer16 = factor-layer
  Full.rotate3Layer16Basis
  Full.rotate3Layer16Row0Mask Full.rotate3Layer16Row1Mask
  Full.rotate3Layer16Row2Mask Full.rotate3Layer16Row3Mask
  Full.rotate3Layer16Row4Mask Full.rotate3Layer16Row5Mask
  Full.rotate3Layer16Row6Mask Full.rotate3Layer16Row7Mask

mkAffine7Layer0 : FactorLayer
mkAffine7Layer0 = factor-layer
  Full.affine7Layer0Basis
  Full.affine7Layer0Row0Mask Full.affine7Layer0Row1Mask
  Full.affine7Layer0Row2Mask Full.affine7Layer0Row3Mask
  Full.affine7Layer0Row4Mask Full.affine7Layer0Row5Mask
  Full.affine7Layer0Row6Mask Full.affine7Layer0Row7Mask

mkAffine7Layer1 : FactorLayer
mkAffine7Layer1 = factor-layer
  Full.affine7Layer1Basis
  Full.affine7Layer1Row0Mask Full.affine7Layer1Row1Mask
  Full.affine7Layer1Row2Mask Full.affine7Layer1Row3Mask
  Full.affine7Layer1Row4Mask Full.affine7Layer1Row5Mask
  Full.affine7Layer1Row6Mask Full.affine7Layer1Row7Mask

mkAffine7Layer16 : FactorLayer
mkAffine7Layer16 = factor-layer
  Full.affine7Layer16Basis
  Full.affine7Layer16Row0Mask Full.affine7Layer16Row1Mask
  Full.affine7Layer16Row2Mask Full.affine7Layer16Row3Mask
  Full.affine7Layer16Row4Mask Full.affine7Layer16Row5Mask
  Full.affine7Layer16Row6Mask Full.affine7Layer16Row7Mask

rotate3FactorStructure : FactorLayerStructure
rotate3FactorStructure =
  factor-layer-structure
    (factor-footprint 0 1 16)
    mkRotate3Layer0 mkRotate3Layer1 mkRotate3Layer16

affine7FactorStructure : FactorLayerStructure
affine7FactorStructure =
  factor-layer-structure
    (factor-footprint 0 1 16)
    mkAffine7Layer0 mkAffine7Layer1 mkAffine7Layer16

rotate3Affine7SameFactorStructure :
  rotate3FactorStructure ≡ affine7FactorStructure
rotate3Affine7SameFactorStructure = refl

rotate3Affine7DifferentGenerator :
  Codec.decodeHybrid Codec.rotate3Hybrid
  ≡ Codec.decodeHybrid Codec.affine7Hybrid → ⊥
rotate3Affine7DifferentGenerator ()

previousCostShapeCollision :
  Cost.codecShape Cost.rotate3Tail ≡ Cost.codecShape Cost.affine7Tail
previousCostShapeCollision = Cost.rotate3Affine7SameCodecShape

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record FactorLayerStructureCollisionBoundary : Set where
  constructor factor-layer-structure-collision-boundary
  field
    previousFullCostShapeCollisionInherited : Bool
    sameFactorModeFootprintZeroOneSixteen : Bool
    sameSelectedBasisOnEveryFactorLayer : Bool
    sameRowMasksOnEveryFactorLayer : Bool
    fullFactorLayerStructureCollisionPaid : Bool
    exactGeneratorIdentityStillSeparatesWitness : Bool
    factorLayerStructureAloneIsGeneratorTerminal : Bool
    complementaryRawModePayloadMustRemainAvailableForExactReplay : Bool
    rawPayloadProvedGloballyMinimalResidual : Bool
    productionRSA260Claimed : Bool
open FactorLayerStructureCollisionBoundary public

canonicalFactorLayerStructureCollisionBoundary :
  FactorLayerStructureCollisionBoundary
canonicalFactorLayerStructureCollisionBoundary =
  factor-layer-structure-collision-boundary
    true
    true
    true
    true
    true
    true
    false
    true
    false
    false

data FactorLayerStructureResidual : Set where
  retainRawModeLayerPayload : FactorLayerStructureResidual
  factorRawModePayloadIntoNextCoarseResidualPair : FactorLayerStructureResidual
  adversariallyAttackRawLayerQuotients : FactorLayerStructureResidual
  testWhetherConsumerCanIgnoreSomeRawLayers : FactorLayerStructureResidual
  recurseUntilConsumerOrExactTerminal : FactorLayerStructureResidual

firstFactorLayerStructureResidual : FactorLayerStructureResidual
firstFactorLayerStructureResidual = retainRawModeLayerPayload

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SameFactorStructureMeansSameGenerator : Set where
data RawResidualMeansGloballyMinimalEncoding : Set where

sameFactorStructureDoesNotCreateGeneratorIdentity :
  SameFactorStructureMeansSameGenerator → ⊥
sameFactorStructureDoesNotCreateGeneratorIdentity ()

rawResidualDoesNotProveGlobalMinimality :
  RawResidualMeansGloballyMinimalEncoding → ⊥
rawResidualDoesNotProveGlobalMinimality ()
