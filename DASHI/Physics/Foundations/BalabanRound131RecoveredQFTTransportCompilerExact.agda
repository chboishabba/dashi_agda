{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanRound131RecoveredQFTTransportCompilerExact where

------------------------------------------------------------------------
-- ROUND131 / RECOVERED-QFT ATTACHMENT -> EXISTING SHARED TRANSPORT DATA
--
-- Preferred same-object order:
--
--   Y = recoverQFT(microscopicState(coarseGrain ...))      [physical seam]
--   recoverQFT(...) = qftTarget(coarseGrain ...)           [QFTRecoveryReceipt]
--   ---------------------------------------------------------------
--   Y = qftTarget(coarseGrain ...)                         [compiler]
--
-- The existing Round131 native-sector transport consumes the last equality.
-- This module makes it downstream compiler output instead of a primitive input.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.BalabanRound131RecoveredQFTAttachmentExact as Attachment
import DASHI.Physics.Foundations.BalabanRound131NativeSectorRecoveryTransportExact as Round131

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact as R131
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record Round131RecoveredQFTTransportInputs
    {U : Weld.UnifiedCandidate}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      domain representation}
    (recovery : R131.CommonMetricReadyBalabanSectorRecovery stressLane)
    (MetricPerturbation VariationScalar : Set) : Set₁ where
  field
    qftRecovery : Weld.QFTRecoveryReceipt U
    recoveredAttachment : Attachment.Round131RecoveredQFTAttachment U Y

    toNativeMetricPerturbation :
      MetricPerturbation → Domain.MetricPerturbation domain

    fromNativeVariationScalar :
      StressRep.PairingScalar representation → VariationScalar

    sharedStressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    literalStressPairingCommutes :
      ∀ perturbation →
      sharedStressMetricPairing
        (Weld.qftSectorStressToShared U group (Top.stressTensor Y group))
        perturbation
      ≡ fromNativeVariationScalar
          (StressRep.stressMetricPairing representation
            (StressRep.stressTensor representation)
            (toNativeMetricPerturbation perturbation))

open Round131RecoveredQFTTransportInputs public

asRound131SharedTransportData :
  ∀ {U trajectory split inputs Y group Scale Volume activity domain representation stressLane}
    {MetricPerturbation VariationScalar : Set}
    (recovery : R131.CommonMetricReadyBalabanSectorRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Round131RecoveredQFTTransportInputs recovery MetricPerturbation VariationScalar →
  Round131.Round131SharedTransportData recovery MetricPerturbation VariationScalar
asRound131SharedTransportData recovery dataSet = record
  { Round131.Round131SharedTransportData.toNativeMetricPerturbation =
      toNativeMetricPerturbation dataSet
  ; Round131.Round131SharedTransportData.fromNativeVariationScalar =
      fromNativeVariationScalar dataSet
  ; Round131.Round131SharedTransportData.literalConstructionIsSelectedQFTTarget =
      Attachment.recoveredAttachmentImpliesSelectedQFTTarget
        (recoveredAttachment dataSet) (qftRecovery dataSet)
  ; Round131.Round131SharedTransportData.sharedStressMetricPairing =
      sharedStressMetricPairing dataSet
  ; Round131.Round131SharedTransportData.literalStressPairingCommutes =
      literalStressPairingCommutes dataSet
  }

round131RecoveredQFTTransportCompilerLevel : ProofLevel
round131RecoveredQFTTransportCompilerLevel = machineChecked

-- The direct target equality is now downstream compiler output on the preferred
-- route.  The recovered-QFT attachment remains the real same-object input.
directSelectedQFTTargetEqualityPrimitive : Bool
directSelectedQFTTargetEqualityPrimitive = false

directSelectedQFTTargetEqualityPrimitiveIsFalse :
  directSelectedQFTTargetEqualityPrimitive ≡ false
directSelectedQFTTargetEqualityPrimitiveIsFalse = refl
