{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PinnedYMGRQFTStressMaxCutExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact as PinnedQFT
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact as Einstein
import DASHI.Physics.Foundations.BalabanAllSectorContinuumProducerExact as Balaban
import DASHI.Physics.Foundations.CommonActionQFTGRContinuumProducerCompilerExact as Common
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned

------------------------------------------------------------------------
-- PINNED-YM / GRQFT STRESS MAX-CUT
--
-- Q1 pays a single same-object construction attachment.  Because the pinned
-- stress is definitionally the literal stress, that same attachment transports
-- every pinned sector stress to actualQFTSectorStressShared.  The total stress
-- weld then needs no further QFT stress-identification theorem.
--
-- Remaining theorem-bearing inputs are exactly:
--   * the all-sector QFT producer, including explicit sector aggregation;
--   * the Einstein common-action metric-variation receipt;
--   * one common metric producer language;
--   * the promotion token (kept separate from mathematics).
------------------------------------------------------------------------

pinnedSectorStressFeedsActualSharedSector :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)}
    (attachment : PinnedQFT.PinnedYangMillsRecoveredQFTAttachment U pinned)
    (qftRecovery : Weld.QFTRecoveryReceipt U)
    candidate regime →
  Weld.qftRegime U regime →
  ∀ group →
  Weld.qftSectorStressToShared U group
      (Pinned.stressTensor (Pinned.local pinned) group)
  ≡ Weld.actualQFTSectorStressShared U
      (Weld.coarseGrain U candidate regime) group
pinnedSectorStressFeedsActualSharedSector =
  PinnedQFT.pinnedSharedSectorStressIsActualSelectedQFTStress

record PinnedYMGRQFTStressMaxCut
    {U : Weld.UnifiedCandidate}
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    (variation : Variation.CommonEffectiveActionVariation U) : Set₁ where
  field
    pinnedRecoveryAttachment :
      PinnedQFT.PinnedYangMillsRecoveredQFTAttachment U pinned

    qftRecovery :
      Weld.QFTRecoveryReceipt U

    einsteinVariation :
      Einstein.EinsteinTensorVariationReceipt variation

    allSectorQFTProducer :
      Balaban.BalabanAllSectorContinuumProducer variation

    commonMetricLanguage :
      Common.CommonMetricProducerLanguage
        einsteinVariation allSectorQFTProducer

    stressWeldToken :
      Weld.StressEnergyWeldToken U

open PinnedYMGRQFTStressMaxCut public

compilePinnedYMGRQFTStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)}
    {variation : Variation.CommonEffectiveActionVariation U} →
  PinnedYMGRQFTStressMaxCut pinned variation →
  Weld.SameStressEnergyWeld U
compilePinnedYMGRQFTStressWeld cut =
  Common.commonEinsteinAndBalabanProducerImpliesStressWeld
    _
    (einsteinVariation cut)
    (allSectorQFTProducer cut)
    (commonMetricLanguage cut)
    (stressWeldToken cut)

data PinnedYMGRQFTStressOpenLeaf : Set where
  missingPinnedLiteralRecoveredQFTAttachment :
    PinnedYMGRQFTStressOpenLeaf
  missingAllSectorAggregationAndCommonVariation :
    PinnedYMGRQFTStressOpenLeaf
  missingEinsteinCommonMetricVariation :
    PinnedYMGRQFTStressOpenLeaf
  missingCommonMetricProducerLanguage :
    PinnedYMGRQFTStressOpenLeaf

canonicalPinnedYMGRQFTStressOpenLeaves :
  List PinnedYMGRQFTStressOpenLeaf
canonicalPinnedYMGRQFTStressOpenLeaves =
  missingPinnedLiteralRecoveredQFTAttachment
  ∷ missingAllSectorAggregationAndCommonVariation
  ∷ missingEinsteinCommonMetricVariation
  ∷ missingCommonMetricProducerLanguage
  ∷ []

secondQFTStressTheoremRequired : Bool
secondQFTStressTheoremRequired = false

secondQFTStressTheoremRequiredIsFalse :
  secondQFTStressTheoremRequired ≡ false
secondQFTStressTheoremRequiredIsFalse = refl
