{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanAllSectorContinuumProducerExact where

------------------------------------------------------------------------
-- BIDI CONSUMER COMPRESSION
--
-- `BalabanSectorMetricVariation` on this branch currently contains one way to
-- manufacture the sector endpoint: finite representation + two convergence
-- theorems + uniqueness.  Downstream QFT/GR unification does not need to know
-- that manufacturing route.  It needs the endpoint identity and exact sector
-- aggregation.
--
-- This module therefore defines the endpoint-only producer consumed by the
-- common-action layer.  The older convergence-rich object remains a valid
-- constructor.  After YM PR #638 joins ancestry, its Round131 source-native
-- sector recovery should provide a second constructor without reintroducing
-- `ConvergesTo` here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact as Legacy
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

record BalabanAllSectorContinuumProducer
    {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) : Set₁ where
  field
    MetricPerturbation VariationScalar : Set

    stressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    SectorAdmissibleMetricPerturbation :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) →
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    sectorContinuumFirstVariation :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) →
      Weld.Candidate U → Weld.Regime U →
      MetricPerturbation → VariationScalar

    sectorContinuumVariationIsLiteralStressPairing :
      ∀ group candidate regime perturbation →
      Weld.qftRegime U regime →
      SectorAdmissibleMetricPerturbation group candidate regime perturbation →
      sectorContinuumFirstVariation group candidate regime perturbation
      ≡ stressMetricPairing
          (Weld.actualQFTSectorStressShared U
            (Weld.coarseGrain U candidate regime) group)
          perturbation

    CommonAdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    commonAdmissibleImpliesSectorAdmissible :
      ∀ group candidate regime perturbation →
      CommonAdmissibleMetricPerturbation candidate regime perturbation →
      SectorAdmissibleMetricPerturbation group candidate regime perturbation

    aggregateSectorStress :
      (QFT.CompactSimpleGroup (Weld.qftCarriers U) → Weld.SharedStressEnergy U) →
      Weld.SharedStressEnergy U

    aggregateVariationScalars :
      (QFT.CompactSimpleGroup (Weld.qftCarriers U) → VariationScalar) →
      VariationScalar

    aggregateVariationScalarsCongruent :
      ∀ left right →
      (∀ group → left group ≡ right group) →
      aggregateVariationScalars left ≡ aggregateVariationScalars right

    aggregateStressPairingCommutes :
      ∀ candidate perturbation →
      stressMetricPairing
        (aggregateSectorStress
          (Weld.actualQFTSectorStressShared U candidate))
        perturbation
      ≡ aggregateVariationScalars
          (λ group →
            stressMetricPairing
              (Weld.actualQFTSectorStressShared U candidate group)
              perturbation)

    commonVariationIsAggregateLiteralSectorStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Variation.effectiveSourceVariation variation
        (Weld.coarseGrain U candidate regime) regime
      ≡ aggregateSectorStress
          (Weld.actualQFTSectorStressShared U
            (Weld.coarseGrain U candidate regime))

    aggregateLiteralSectorStressIsDeclaredTotal :
      ∀ candidate →
      aggregateSectorStress
        (Weld.actualQFTSectorStressShared U candidate)
      ≡ Weld.qftTotalStressShared U candidate

    literalSectorStressAggregates :
      ∀ candidate →
      Weld.QFTStressAggregation U candidate
        (Weld.actualQFTSectorStressShared U candidate)
        (Weld.qftTotalStressShared U candidate)

open BalabanAllSectorContinuumProducer public

legacyReceiptToContinuumProducer :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U} →
  Legacy.BalabanAllSectorVariationReceipt variation →
  BalabanAllSectorContinuumProducer variation
legacyReceiptToContinuumProducer receipt = record
  { MetricPerturbation = Legacy.MetricPerturbation receipt
  ; VariationScalar = Legacy.VariationScalar receipt
  ; stressMetricPairing = Legacy.stressMetricPairing receipt
  ; SectorAdmissibleMetricPerturbation = λ group →
      Legacy.AdmissibleMetricPerturbation (Legacy.sectorVariation receipt group)
  ; sectorContinuumFirstVariation = λ group →
      Legacy.continuumFirstVariation (Legacy.sectorVariation receipt group)
  ; sectorContinuumVariationIsLiteralStressPairing =
      λ group candidate regime perturbation qftAtRegime admissible →
        Legacy.balabanSectorContinuumFirstVariationIsLiteralStressPairing
          (Legacy.sectorVariation receipt group)
          candidate regime perturbation qftAtRegime admissible
  ; CommonAdmissibleMetricPerturbation =
      Legacy.CommonAdmissibleMetricPerturbation receipt
  ; commonAdmissibleImpliesSectorAdmissible =
      Legacy.commonAdmissibleImpliesSectorAdmissible receipt
  ; aggregateSectorStress = Legacy.aggregateSectorStress receipt
  ; aggregateVariationScalars = Legacy.aggregateVariationScalars receipt
  ; aggregateVariationScalarsCongruent =
      Legacy.aggregateVariationScalarsCongruent receipt
  ; aggregateStressPairingCommutes = Legacy.aggregateStressPairingCommutes receipt
  ; commonVariationIsAggregateLiteralSectorStress =
      Legacy.commonVariationIsAggregateLiteralSectorStress receipt
  ; aggregateLiteralSectorStressIsDeclaredTotal =
      Legacy.aggregateLiteralSectorStressIsDeclaredTotal receipt
  ; literalSectorStressAggregates = Legacy.literalSectorStressAggregates receipt
  }

aggregateSectorVariationIsAggregateStressPairing :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    (producer : BalabanAllSectorContinuumProducer variation)
    candidate regime perturbation →
  Weld.qftRegime U regime →
  CommonAdmissibleMetricPerturbation producer candidate regime perturbation →
  aggregateVariationScalars producer
    (λ group → sectorContinuumFirstVariation producer group
      candidate regime perturbation)
  ≡ stressMetricPairing producer
      (aggregateSectorStress producer
        (Weld.actualQFTSectorStressShared U
          (Weld.coarseGrain U candidate regime)))
      perturbation
aggregateSectorVariationIsAggregateStressPairing
    producer candidate regime perturbation qftAtRegime commonAdmissible =
  trans
    (aggregateVariationScalarsCongruent producer _ _
      (λ group →
        sectorContinuumVariationIsLiteralStressPairing producer
          group candidate regime perturbation qftAtRegime
          (commonAdmissibleImpliesSectorAdmissible producer
            group candidate regime perturbation commonAdmissible)))
    (sym (aggregateStressPairingCommutes producer
      (Weld.coarseGrain U candidate regime) perturbation))

continuumProducerBuildsQFTVariationIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U} →
  BalabanAllSectorContinuumProducer variation →
  Variation.QFTVariationIdentification variation
continuumProducerBuildsQFTVariationIdentification producer = record
  { Variation.QFTVariationIdentification.literalQFTStressAggregates =
      literalSectorStressAggregates producer
  ; Variation.QFTVariationIdentification.variationEqualsTotalQFTStress =
      λ candidate regime qftAtRegime →
        trans
          (commonVariationIsAggregateLiteralSectorStress
            producer candidate regime qftAtRegime)
          (aggregateLiteralSectorStressIsDeclaredTotal producer
            (Weld.coarseGrain U candidate regime))
  }

balabanContinuumProducerCompilerLevel : ProofLevel
balabanContinuumProducerCompilerLevel = machineChecked

record BalabanContinuumProducerBoundary : Set where
  constructor balabanContinuumProducerBoundary
  field
    downstreamCommonActionNeedsIndependentConvergenceRelation : Bool
    downstreamCommonActionNeedsIndependentConvergenceRelationIsFalse :
      downstreamCommonActionNeedsIndependentConvergenceRelation ≡ false

    endpointSectorVariationPlusExactAggregationIsSufficient : Bool
    endpointSectorVariationPlusExactAggregationIsSufficientIsTrue :
      endpointSectorVariationPlusExactAggregationIsSufficient ≡ true

canonicalBalabanContinuumProducerBoundary : BalabanContinuumProducerBoundary
canonicalBalabanContinuumProducerBoundary =
  balabanContinuumProducerBoundary false refl true refl
