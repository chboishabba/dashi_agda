{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralFiniteMeasureStressLaneRound125Exact where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record LiteralFiniteMeasureStressLane
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
    measureWeld : R124.BalabanDensityLiteralFiniteMeasureWeld
      {trajectory = trajectory} {split = split} {inputs = inputs}
      Y group
open LiteralFiniteMeasureStressLane public

selectedStressDensityIsLiteralClayFiniteMeasure :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation stressLane}
    (dataSet : LiteralFiniteMeasureStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  let selectedScale =
        R122.selectedDensityScale (R123.densityAnchor stressLane)
  in
  R124.densityToFiniteMeasure (measureWeld dataSet)
    (BetaDensity.densityAt inputs selectedScale)
  ≡ Top.finiteMeasure Y group
      (R124.cutoffAtScale (measureWeld dataSet) selectedScale)
selectedStressDensityIsLiteralClayFiniteMeasure
    {stressLane = stressLane} dataSet =
  R124.densityAtScaleIsLiteralFiniteMeasure (measureWeld dataSet)
    (R122.selectedDensityScale (R123.densityAnchor stressLane))

literalFiniteMeasureStressLaneCompilerLevel : ProofLevel
literalFiniteMeasureStressLaneCompilerLevel = machineChecked

literalBalabanStressDensityIsClayFiniteMeasureLevel : ProofLevel
literalBalabanStressDensityIsClayFiniteMeasureLevel = conditional
