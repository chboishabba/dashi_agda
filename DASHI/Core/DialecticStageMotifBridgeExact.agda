module DASHI.Core.DialecticStageMotifBridgeExact where

------------------------------------------------------------------------
-- STAGE / MOTIF BRIDGE
--
-- The recovered history distinguishes the broad 0--11 dialectical stage
-- spectrum from the later executable M1--M10 motif classifier.  This module
-- records only explicit correspondences that current code actually supports.
-- It does not define a total Stage -> Motif or Motif -> Stage conversion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.DialecticalStageSpectrumExact as Stage
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Reasoning.DialecticMotifKernel as Motif

------------------------------------------------------------------------
-- Closure/lift analogy: both systems have an explicit post-local lift role,
-- but they remain differently typed constructions.
------------------------------------------------------------------------

stage10IsNewAxisLift :
  Stage.stageRole Stage.stage10 ≡ Stage.newAxisLift
stage10IsNewAxisLift = refl

motifM10PolicyIsLift :
  Motif.policy Motif.M10 ≡ Motif.lift
motifM10PolicyIsLift = refl

carryVoxelProducesM10 :
  Motif.supervise Motif.carryVoxel Motif.allGreen ≡ Motif.M10
carryVoxelProducesM10 =
  Motif.carry-classifies

------------------------------------------------------------------------
-- The historical neutral/refine rule and operational M5 buffer can be related
-- only through an explicit bridge.  They are not definitions of one another.
------------------------------------------------------------------------

neutralEvidenceSuspends :
  Suspension.disposition Suspension.neutralEvidence
  ≡ Suspension.suspendAndRefine
neutralEvidenceSuspends = refl

zeroTensorCurrentlyClassifiesM5 :
  Motif.supervise Motif.withinVoxel Motif.zeroState ≡ Motif.M5
zeroTensorCurrentlyClassifiesM5 =
  Motif.zero-classifies

m5PolicyCurrentlyBuffers :
  Motif.policy Motif.M5 ≡ Motif.buffer
m5PolicyCurrentlyBuffers = refl

record DialecticStageMotifBoundary : Set where
  constructor dialectic-stage-motif-boundary
  field
    stage5DefinitionIsMotifM5 : Bool
    stage5DefinitionIsMotifM5IsFalse : stage5DefinitionIsMotifM5 ≡ false
    stage9DefinitionIsMotifM9 : Bool
    stage9DefinitionIsMotifM9IsFalse : stage9DefinitionIsMotifM9 ≡ false
    stage10DefinitionIsMotifM10 : Bool
    stage10DefinitionIsMotifM10IsFalse : stage10DefinitionIsMotifM10 ≡ false
    stage11RequiresMotifM11 : Bool
    stage11RequiresMotifM11IsFalse : stage11RequiresMotifM11 ≡ false

canonicalDialecticStageMotifBoundary : DialecticStageMotifBoundary
canonicalDialecticStageMotifBoundary =
  dialectic-stage-motif-boundary
    false refl
    false refl
    false refl
    false refl
