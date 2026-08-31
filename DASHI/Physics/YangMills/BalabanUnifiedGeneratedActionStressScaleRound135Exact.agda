{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact where

------------------------------------------------------------------------
-- ROUND135: ONE SOURCE SCALE FOR BC1/BC2 AND THE STRESS DENSITY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as DensityAnchor
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record UnifiedGeneratedActionStressScale
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld}
    {metricInputs : R134.PresentCutMetricSpecificInputs firstWeld}
    {representation : StressRep.CanonicalMetricStressRepresentation
      (R134.presentCutCanonicalMetricDomain metricInputs)}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (lane : StressLane.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      (R134.presentCutCanonicalMetricDomain metricInputs) representation) : Set₁ where
  field
    stressSelectedScaleIsBC1Scale :
      DensityAnchor.selectedScale (StressLane.densityAnchor lane)
      ≡ Carrier.scale (Present.bc1Carrier present)

    stressScaleIndexAgreesWithUnifiedAction :
      DensityAnchor.sourceScaleIndex (StressLane.densityAnchor lane)
        (Carrier.scale (Present.bc1Carrier present))
      ≡ R132.sourceScaleToDensityIndex actionWeld
          (Carrier.scale (Present.bc1Carrier present))

open UnifiedGeneratedActionStressScale public

stressSelectedDensityIndexIsUnifiedActionIndex :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      metricInputs representation C S Y group lane}
    (weld : UnifiedGeneratedActionStressScale
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} {actionWeld = actionWeld} {firstWeld = firstWeld}
      {metricInputs = metricInputs} {representation = representation}
      {C = C} {S = S} {Y = Y} {group = group} lane) →
  DensityAnchor.selectedDensityScale (StressLane.densityAnchor lane)
  ≡ R132.selectedDensityIndex actionWeld
stressSelectedDensityIndexIsUnifiedActionIndex
    {present = present} {actionWeld = actionWeld} {lane = lane} weld =
  trans
    (cong (DensityAnchor.sourceScaleIndex (StressLane.densityAnchor lane))
      (stressSelectedScaleIsBC1Scale weld))
    (stressScaleIndexAgreesWithUnifiedAction weld)

unifiedGeneratedActionStressScaleCompilerLevel : ProofLevel
unifiedGeneratedActionStressScaleCompilerLevel = machineChecked

literalUnifiedGeneratedActionStressScaleLevel : ProofLevel
literalUnifiedGeneratedActionStressScaleLevel = conditional
