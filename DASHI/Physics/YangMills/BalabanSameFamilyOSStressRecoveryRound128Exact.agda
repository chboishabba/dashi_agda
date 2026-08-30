{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact where

------------------------------------------------------------------------
-- ROUND128: BALABAN FINITE FAMILY, OS SYSTEM, AND STRESS SHARE ONE CONTINUUM
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanLiteralSchwingerStressRecoveryRound126Exact as R126
import DASHI.Physics.YangMills.BalabanOSLiteralSchwingerWeldRound127Exact as R127
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record SameFamilyOSStressRecovery
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
    schwingerRecovery : R126.LiteralBalabanSchwingerStressRecovery stressLane
    osWeld : R127.OSLiteralSchwingerWeld Y group
open SameFamilyOSStressRecovery public

sourceOSImageBelongsToSameContinuumMeasure :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation stressLane}
    (dataSet : SameFamilyOSStressRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y group)
    (R127.sourceSystemToLiteralSchwinger (osWeld dataSet)
      (R127.sourceOSSystem (osWeld dataSet)))
sourceOSImageBelongsToSameContinuumMeasure
    {S = S} {Y = Y} {group = group} dataSet =
  subst
    (λ selected → Top.SchwingerBelongsToMeasure S
      (Top.continuumMeasure Y group) selected)
    (sym (R127.sourceOSSystemIsLiteralSchwinger (osWeld dataSet)))
    (R126.literalSchwingerBelongsToContinuumMeasure
      (schwingerRecovery dataSet))

sameFamilyOSStressRecoveryCompilerLevel : ProofLevel
sameFamilyOSStressRecoveryCompilerLevel = machineChecked

-- Physical input remaining: instantiate the source OS-to-literal Schwinger weld
-- and the finite-measure continuum-limit evidence on the actual Balaban family.
literalBalabanSameFamilyOSStressRecoveryLevel : ProofLevel
literalBalabanSameFamilyOSStressRecoveryLevel = conditional
