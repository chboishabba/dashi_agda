{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119R129PaysContinuumSemanticsRound430Exact where

------------------------------------------------------------------------
-- A/C / ROUND430: R129 RECOVERY PAYS CONTINUUM-LIMIT + SCHWINGER SEMANTICS
--
-- These are not independent A leaves once the same-family R129 recovery exists.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

continuumLimitFromR129 :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  R129.BalabanSectorQFTRecoveryExport stressLane →
  Top.IsContinuumLimitOf S group
    (Top.finiteMeasure Y group)
    (Top.continuumMeasure Y group)
continuumLimitFromR129 =
  R129.literalContinuumMeasureRecovery

schwingerBelongsToSameContinuumMeasureFromR129 :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  R129.BalabanSectorQFTRecoveryExport stressLane →
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y group)
    (Top.schwinger Y group)
schwingerBelongsToSameContinuumMeasureFromR129 =
  R129.literalSchwingerRecovery

round430ContinuumSemanticsFromR129CompilerLevel : ProofLevel
round430ContinuumSemanticsFromR129CompilerLevel = machineChecked

round430IndependentAContinuumLimitLeafRequired : ProofLevel
round430IndependentAContinuumLimitLeafRequired = machineChecked

round430IndependentASchwingerMembershipLeafRequired : ProofLevel
round430IndependentASchwingerMembershipLeafRequired = machineChecked

-- The R129 recovery itself remains a physical source inhabitant.  This owner
-- only records that A8/A9 are not additional theorems after that inhabitant.
literalRound430R129RecoveryLevel : ProofLevel
literalRound430R129RecoveryLevel = conditional
