{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact where

------------------------------------------------------------------------
-- ROUND136: FROZEN A/BC GENERATED ACTION -> COMMON-METRIC SCHWINGER STRESS
--
-- This is the post-merge BIDI cross-pollination capstone.  It does not introduce
-- another effective action, density, radius, convergence relation or stress
-- tensor.  It requires the existing Round129/130 endpoint evidence on a stress
-- lane already welded by Rounds132--135 to the exact Round122 BC1/BC2 action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact as R130
import DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact as R131
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record UnifiedGeneratedActionSectorRecovery
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
    {lane : StressLane.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      (R134.presentCutCanonicalMetricDomain metricInputs) representation}
    (scaleWeld : R135.UnifiedGeneratedActionStressScale lane) : Set₁ where
  field
    qftRecovery : R129.BalabanSectorQFTRecoveryExport lane
    metricPairing : R130.ContinuumMetricStressPairingWeld lane

open UnifiedGeneratedActionSectorRecovery public

asCommonMetricReadyBalabanSectorRecovery :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      metricInputs representation C S Y group lane scaleWeld} →
  UnifiedGeneratedActionSectorRecovery
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld} {firstWeld = firstWeld}
    {metricInputs = metricInputs} {representation = representation}
    {C = C} {S = S} {Y = Y} {group = group} scaleWeld →
  R131.CommonMetricReadyBalabanSectorRecovery lane
asCommonMetricReadyBalabanSectorRecovery recovery = record
  { R131.CommonMetricReadyBalabanSectorRecovery.qftRecovery = qftRecovery recovery
  ; R131.CommonMetricReadyBalabanSectorRecovery.metricPairing = metricPairing recovery
  }

continuumFirstVariationOfUnifiedGeneratedActionIsLiteralStressPairing :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      metricInputs representation C S Y group lane scaleWeld}
    (recovery : UnifiedGeneratedActionSectorRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} {actionWeld = actionWeld} {firstWeld = firstWeld}
      {metricInputs = metricInputs} {representation = representation}
      {C = C} {S = S} {Y = Y} {group = group} scaleWeld) →
  ∀ perturbation →
  let domain = R134.presentCutCanonicalMetricDomain metricInputs
  in
  Domain.AdmissibleMetricPerturbation domain perturbation →
  R131.continuumSectorFirstVariation
      (asCommonMetricReadyBalabanSectorRecovery recovery) perturbation
  ≡ StressRep.stressMetricPairing representation
      (StressRep.stressTensor representation) perturbation
continuumFirstVariationOfUnifiedGeneratedActionIsLiteralStressPairing recovery =
  R131.continuumSectorFirstVariationIsLiteralStressPairing
    (asCommonMetricReadyBalabanSectorRecovery recovery)

unifiedGeneratedActionRecoveryCompilerLevel : ProofLevel
unifiedGeneratedActionRecoveryCompilerLevel = machineChecked

-- Remaining physical seam is now source instantiation, not parallel recovery:
-- instantiate R132 same-action representation, R133 first-order identification,
-- the metric-specific tangent admission, the stress coordinate/source evidence,
-- and the already-separated finite-measure/Schwinger endpoint receipts.
literalUnifiedGeneratedActionSectorRecoveryLevel : ProofLevel
literalUnifiedGeneratedActionSectorRecoveryLevel = conditional
