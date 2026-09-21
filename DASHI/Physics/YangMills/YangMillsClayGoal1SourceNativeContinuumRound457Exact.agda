{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1SourceNativeContinuumRound457Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND457: SOURCE-NATIVE A3 + SAME-OS COMPATIBILITY.
--
-- The direct-source manuscript historically counted
--
--   H2(i) continuum recovery
--   H3     same reconstructed Hamiltonian/correlation
--
-- as separate mass-gap-side inputs, and used projective Prokhorov as the
-- principal A3 route.
--
-- Round126--128 already expose a stronger SAME-FAMILY alternative:
--
--   literal Balaban finite family
--       -> literal Clay continuum limit
--       -> literal Clay Schwinger family
--       -> source OS system welded to that SAME Schwinger family.
--
-- Thus:
--   * H3 is common continuum/OS compatibility, not a B research theorem;
--   * projective compactness is an A3 fallback, not mandatory when this
--     source-native recovery is inhabited.
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanLiteralSchwingerStressRecoveryRound126Exact as R126
import DASHI.Physics.YangMills.BalabanOSLiteralSchwingerWeldRound127Exact as R127
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record SourceNativeContinuumAndOS
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) : Set₁ where
  field
    sameFamilyRecovery : R128.SameFamilyOSStressRecovery stressLane

open SourceNativeContinuumAndOS public

literalContinuumAndSchwinger :
  ∀ {trajectory split inputs C S Y group Scale Volume activity
      domain representation stressLane}
    (dataSet : SourceNativeContinuumAndOS
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Top.IsContinuumLimitOf S group
    (Top.finiteMeasure Y group)
    (Top.continuumMeasure Y group)
  ×
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y group)
    (Top.schwinger Y group)
literalContinuumAndSchwinger dataSet =
  let recovery = R128.schwingerRecovery (sameFamilyRecovery dataSet)
  in
  R126.literalFiniteMeasuresConverge recovery ,
  R126.literalSchwingerBelongsToContinuumMeasure recovery

sourceOSSystemBelongsToLiteralContinuumMeasure :
  ∀ {trajectory split inputs C S Y group Scale Volume activity
      domain representation stressLane}
    (dataSet : SourceNativeContinuumAndOS
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  let osWeld = R128.osWeld (sameFamilyRecovery dataSet)
  in
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y group)
    (R127.sourceSystemToLiteralSchwinger osWeld
      (R127.sourceOSSystem osWeld))
sourceOSSystemBelongsToLiteralContinuumMeasure dataSet =
  R128.sourceOSImageBelongsToSameContinuumMeasure
    (sameFamilyRecovery dataSet)

round457SourceNativeContinuumOSCompilerLevel : ProofLevel
round457SourceNativeContinuumOSCompilerLevel =
  R128.sameFamilyOSStressRecoveryCompilerLevel

-- The sole physical theorem on this route is the actual finite-measure
-- continuum recovery plus source-OS/literal-Schwinger weld on the literal
-- Balaban family.  It is an A/common-OS payment, not a B payment.
literalRound457SourceNativeContinuumOSLevel : ProofLevel
literalRound457SourceNativeContinuumOSLevel =
  R128.literalBalabanSameFamilyOSStressRecoveryLevel
