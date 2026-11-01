module DASHI.ComputerScience.RSA260BidiHybridTailCostShapeCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact as Codec

------------------------------------------------------------------------
-- DESCENDING BELOW THE HYBRID TAIL
--
-- The first recursive untangling step below HybridEncodedGenerator should not
-- simply rename generator identity as the next coarse coordinate. Attack a
-- cheaper candidate first: the complete currently-recorded codec cost shape
-- (raw bits, description bits, witness bits, decode XOR work, savings).
--
-- rotate3 and affine7 collide on this entire shape while decoding to different
-- generator identities. Therefore even the combined description/witness/
-- execution summary is not a consumer terminal for exact generator identity.
-- The relative-fine coordinate must retain more structural information.
------------------------------------------------------------------------

record CodecShape : Set where
  constructor codec-shape
  field
    rawBits : Nat
    descriptionBits : Nat
    witnessBits : Nat
    decodeXorOps : Nat
    savedBits : Nat
open CodecShape public

shapeFromCost : Codec.CodecCost → CodecShape
shapeFromCost cost =
  codec-shape
    (Codec.rawCoefficientBits cost)
    (Codec.descriptionBits cost)
    (Codec.witnessBits cost)
    (Codec.decodeXorOps cost)
    (Codec.bitsSavedVsRaw cost)

codecShape : Codec.HybridEncodedGenerator → CodecShape
codecShape tail = shapeFromCost (Codec.costOf (Codec.decodeHybrid tail))

rotate3Tail : Codec.HybridEncodedGenerator
rotate3Tail = Codec.rotate3Hybrid

affine7Tail : Codec.HybridEncodedGenerator
affine7Tail = Codec.affine7Hybrid

rotate3Affine7SameCodecShape :
  codecShape rotate3Tail ≡ codecShape affine7Tail
rotate3Affine7SameCodecShape = refl

rotate3Affine7DifferentGenerator :
  Codec.decodeHybrid rotate3Tail ≡ Codec.decodeHybrid affine7Tail → ⊥
rotate3Affine7DifferentGenerator ()

------------------------------------------------------------------------
-- Exact reopening keeps generator identity as the residual for this attacked
-- quotient. The next research step is to replace that residual by explicit
-- layer mode/basis/mask structure and attack again.
------------------------------------------------------------------------

reopenHybridTail :
  CodecShape → Codec.SyntheticGenerator → Codec.HybridEncodedGenerator
reopenHybridTail _ generator = Codec.encodeHybrid generator

reopenHybridTailExact :
  (tail : Codec.HybridEncodedGenerator) →
  reopenHybridTail (codecShape tail) (Codec.decodeHybrid tail) ≡ tail
reopenHybridTailExact Codec.identityHybrid = refl
reopenHybridTailExact Codec.rotate1Hybrid = refl
reopenHybridTailExact Codec.rotate2Hybrid = refl
reopenHybridTailExact Codec.rotate3Hybrid = refl
reopenHybridTailExact Codec.affine3Hybrid = refl
reopenHybridTailExact Codec.affine5Hybrid = refl
reopenHybridTailExact Codec.affine7Hybrid = refl
reopenHybridTailExact Codec.affine9Hybrid = refl
reopenHybridTailExact Codec.xor1Hybrid = refl
reopenHybridTailExact Codec.bitrev9Hybrid = refl

hybridTailCostShapeGeometry :
  Fibre.CoarseFineReopening Codec.HybridEncodedGenerator
hybridTailCostShapeGeometry =
  Fibre.coarseFineReopening
    CodecShape
    Codec.SyntheticGenerator
    codecShape
    Codec.decodeHybrid
    reopenHybridTail
    reopenHybridTailExact

exactGeneratorIdentityFineSensitive :
  Fibre.FineSensitiveConsumer hybridTailCostShapeGeometry Codec.decodeHybrid
exactGeneratorIdentityFineSensitive =
  Fibre.fineSensitiveConsumer
    rotate3Tail
    affine7Tail
    rotate3Affine7SameCodecShape
    rotate3Affine7DifferentGenerator
    "rotate3/affine7: same full codec cost shape, different recovered generator identity"

costShapeRefutesGeneratorIdentityReduction :
  ∀ {Action : Set}
    {step : Action → Codec.HybridEncodedGenerator → Codec.HybridEncodedGenerator} →
  Reduction.CandidateReductionFailure step Codec.decodeHybrid codecShape
costShapeRefutesGeneratorIdentityReduction =
  Fibre.fineSensitivityRefutesCoarseOnlyReduction
    hybridTailCostShapeGeometry
    exactGeneratorIdentityFineSensitive

------------------------------------------------------------------------
-- Boundary / next residual.
------------------------------------------------------------------------

record HybridTailCostShapeCollisionBoundary : Set where
  constructor hybrid-tail-cost-shape-collision-boundary
  field
    descendsBelowCurrentHybridTail : Bool
    descriptionWitnessExecutionAxesRetainedTogether : Bool
    rotate3Affine7FullCostShapeCollisionPaid : Bool
    exactGeneratorIdentityStillSeparatesCollision : Bool
    costShapeAloneIsConsumerTerminalForGeneratorIdentity : Bool
    exactReopeningRetainsGeneratorResidual : Bool
    explicitLayerModeBasisMaskStructureAttackedHere : Bool
    productionRSA260Claimed : Bool
open HybridTailCostShapeCollisionBoundary public

canonicalHybridTailCostShapeCollisionBoundary :
  HybridTailCostShapeCollisionBoundary
canonicalHybridTailCostShapeCollisionBoundary =
  hybrid-tail-cost-shape-collision-boundary
    true
    true
    true
    true
    false
    true
    false
    false

data HybridTailCostShapeResidual : Set where
  attackExplicitLayerModeBasisMaskStructure : HybridTailCostShapeResidual
  factorLayerModeProfileIntoCoarseAndResidual : HybridTailCostShapeResidual
  adversariallySearchLayerStructureCollisions : HybridTailCostShapeResidual
  retainBasisMaskResidualOnlyWhenConsumerRequiresIt : HybridTailCostShapeResidual
  recurseUntilConsumerOrExactTerminal : HybridTailCostShapeResidual

firstHybridTailCostShapeResidual : HybridTailCostShapeResidual
firstHybridTailCostShapeResidual = attackExplicitLayerModeBasisMaskStructure
