{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedPresentCutSchwingerRecoveryRound140Exact where

------------------------------------------------------------------------
-- ROUND140: ONE PHYSICAL SOURCE OBJECT SPANS THE FROZEN CUT AND SCHWINGER STRESS
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (1ℚ; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanA2PresentCutFallbackRound120Exact as A2
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as Heat
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionPhysicalHistoryRound139Exact as R139
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record UnifiedPresentCutSchwingerRecovery
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
    {scaleWeld : R135.UnifiedGeneratedActionStressScale lane} : Set₁ where
  field
    physicalHistory : R139.UnifiedGeneratedActionPhysicalHistory actionWeld
    sectorRecovery : R136.UnifiedGeneratedActionSectorRecovery scaleWeld

open UnifiedPresentCutSchwingerRecovery public

-- A2's complete finite-prefix contraction is now a projection of an object whose
-- coupling history is already tied to the density feeding BC1/BC2/stress.
unifiedA2FullPrefixBelowOne :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      metricInputs representation C S Y group lane scaleWeld} →
  UnifiedPresentCutSchwingerRecovery
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld} {firstWeld = firstWeld}
    {metricInputs = metricInputs} {representation = representation}
    {C = C} {S = S} {Y = Y} {group = group}
    {lane = lane} {scaleWeld = scaleWeld} →
  A2.presentCutTotalSensitivity (Present.a2 present) cutoff < 1ℚ
unifiedA2FullPrefixBelowOne {present = present} _ =
  Present.a2TotalSensitivityFullPrefixBelowOne present

-- The exact BC1 carrier is exposed unchanged.  Its effective potential is the
-- one represented by the Round132 selected beta-driven density.
unifiedBC1Carrier :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      metricInputs representation C S Y group lane scaleWeld} →
  UnifiedPresentCutSchwingerRecovery
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld} {firstWeld = firstWeld}
    {metricInputs = metricInputs} {representation = representation}
    {C = C} {S = S} {Y = Y} {group = group}
    {lane = lane} {scaleWeld = scaleWeld} →
  Carrier.LiteralDifferentiatedEffectiveDensityCarrier
unifiedBC1Carrier {present = present} _ = Present.bc1Carrier present

-- BC2 remains definitionally on that exact BC1 carrier.
unifiedBC2SameDensityCalculus :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      metricInputs representation C S Y group lane scaleWeld} →
  UnifiedPresentCutSchwingerRecovery
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld} {firstWeld = firstWeld}
    {metricInputs = metricInputs} {representation = representation}
    {C = C} {S = S} {Y = Y} {group = group}
    {lane = lane} {scaleWeld = scaleWeld} →
  Heat.HeatDoobSameDensityCalculus (Present.bc1Carrier present)
unifiedBC2SameDensityCalculus {present = present} _ =
  Present.bc2SameDensityCalculus present

unifiedContinuumFirstVariationIsLiteralStressPairing :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      metricInputs representation C S Y group lane scaleWeld}
    (recovery : UnifiedPresentCutSchwingerRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} {actionWeld = actionWeld} {firstWeld = firstWeld}
      {metricInputs = metricInputs} {representation = representation}
      {C = C} {S = S} {Y = Y} {group = group}
      {lane = lane} {scaleWeld = scaleWeld}) →
  ∀ perturbation →
  Domain.AdmissibleMetricPerturbation
    (R134.presentCutCanonicalMetricDomain metricInputs) perturbation →
  DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact.continuumSectorFirstVariation
      (R136.asCommonMetricReadyBalabanSectorRecovery (sectorRecovery recovery))
      perturbation
  ≡ StressRep.stressMetricPairing representation
      (StressRep.stressTensor representation) perturbation
unifiedContinuumFirstVariationIsLiteralStressPairing recovery =
  R136.continuumFirstVariationOfUnifiedGeneratedActionIsLiteralStressPairing
    (sectorRecovery recovery)

unifiedPresentCutSchwingerRecoveryCompilerLevel : ProofLevel
unifiedPresentCutSchwingerRecoveryCompilerLevel = machineChecked

literalUnifiedPresentCutSchwingerRecoveryLevel : ProofLevel
literalUnifiedPresentCutSchwingerRecoveryLevel = conditional
