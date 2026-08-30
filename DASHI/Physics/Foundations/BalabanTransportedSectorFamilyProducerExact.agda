{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanTransportedSectorFamilyProducerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.BalabanAllSectorContinuumProducerExact as Producer
import DASHI.Physics.Foundations.BalabanNativeSectorRecoveryTransportExact as Transport
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

------------------------------------------------------------------------
-- A family of native sector endpoint transports plus explicit aggregation is
-- sufficient to construct the endpoint-only QFT producer.  The construction
-- never mentions how any native endpoint was proved.
------------------------------------------------------------------------

record TransportedBalabanSectorFamily
    {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) : Set₁ where
  field
    MetricPerturbation VariationScalar : Set

    sectorTransport :
      (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
      Transport.NativeBalabanSectorRecoveryTransport
        group MetricPerturbation VariationScalar

    -- One QFT-side pairing convention is shared by every sector transport.
    commonSectorPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    sectorPairingIsCommon :
      ∀ group stress perturbation →
      Transport.sharedStressMetricPairing (sectorTransport group)
        stress perturbation
      ≡ commonSectorPairing stress perturbation

    CommonAdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    commonAdmissibleImpliesTransportedAdmissible :
      ∀ group candidate regime perturbation →
      CommonAdmissibleMetricPerturbation candidate regime perturbation →
      Transport.TransportedAdmissibleMetricPerturbation
        (sectorTransport group) perturbation

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
      commonSectorPairing
        (aggregateSectorStress
          (Weld.actualQFTSectorStressShared U candidate))
        perturbation
      ≡ aggregateVariationScalars
          (λ group →
            commonSectorPairing
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

open TransportedBalabanSectorFamily public

transportedSectorIdentityWithCommonPairing :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    (family : TransportedBalabanSectorFamily variation)
    group candidate regime perturbation →
  Weld.qftRegime U regime →
  Transport.TransportedAdmissibleMetricPerturbation
    (sectorTransport family group) perturbation →
  Transport.transportedSectorContinuumFirstVariation
    (sectorTransport family group) perturbation
  ≡ commonSectorPairing family
      (Weld.actualQFTSectorStressShared U
        (Weld.coarseGrain U candidate regime) group)
      perturbation
transportedSectorIdentityWithCommonPairing
    family group candidate regime perturbation qftAtRegime admissible =
  trans
    (Transport.transportedSectorVariationIsActualSharedStressPairing
      (sectorTransport family group)
      candidate regime perturbation qftAtRegime admissible)
    (sectorPairingIsCommon family group
      (Weld.actualQFTSectorStressShared U
        (Weld.coarseGrain U candidate regime) group)
      perturbation)

transportedSectorFamilyToContinuumProducer :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U} →
  TransportedBalabanSectorFamily variation →
  Producer.BalabanAllSectorContinuumProducer variation
transportedSectorFamilyToContinuumProducer family = record
  { Producer.BalabanAllSectorContinuumProducer.MetricPerturbation =
      MetricPerturbation family
  ; Producer.BalabanAllSectorContinuumProducer.VariationScalar =
      VariationScalar family
  ; Producer.BalabanAllSectorContinuumProducer.stressMetricPairing =
      commonSectorPairing family
  ; Producer.BalabanAllSectorContinuumProducer.SectorAdmissibleMetricPerturbation =
      λ group _ _ perturbation →
        Transport.TransportedAdmissibleMetricPerturbation
          (sectorTransport family group) perturbation
  ; Producer.BalabanAllSectorContinuumProducer.sectorContinuumFirstVariation =
      λ group _ _ perturbation →
        Transport.transportedSectorContinuumFirstVariation
          (sectorTransport family group) perturbation
  ; Producer.BalabanAllSectorContinuumProducer.sectorContinuumVariationIsLiteralStressPairing =
      λ group candidate regime perturbation qftAtRegime admissible →
        transportedSectorIdentityWithCommonPairing
          family group candidate regime perturbation qftAtRegime admissible
  ; Producer.BalabanAllSectorContinuumProducer.CommonAdmissibleMetricPerturbation =
      CommonAdmissibleMetricPerturbation family
  ; Producer.BalabanAllSectorContinuumProducer.commonAdmissibleImpliesSectorAdmissible =
      commonAdmissibleImpliesTransportedAdmissible family
  ; Producer.BalabanAllSectorContinuumProducer.aggregateSectorStress =
      aggregateSectorStress family
  ; Producer.BalabanAllSectorContinuumProducer.aggregateVariationScalars =
      aggregateVariationScalars family
  ; Producer.BalabanAllSectorContinuumProducer.aggregateVariationScalarsCongruent =
      aggregateVariationScalarsCongruent family
  ; Producer.BalabanAllSectorContinuumProducer.aggregateStressPairingCommutes =
      aggregateStressPairingCommutes family
  ; Producer.BalabanAllSectorContinuumProducer.commonVariationIsAggregateLiteralSectorStress =
      commonVariationIsAggregateLiteralSectorStress family
  ; Producer.BalabanAllSectorContinuumProducer.aggregateLiteralSectorStressIsDeclaredTotal =
      aggregateLiteralSectorStressIsDeclaredTotal family
  ; Producer.BalabanAllSectorContinuumProducer.literalSectorStressAggregates =
      literalSectorStressAggregates family
  }

transportedSectorFamilyProducerCompilerLevel : ProofLevel
transportedSectorFamilyProducerCompilerLevel = machineChecked

record TransportedSectorFamilyBoundary : Set where
  constructor transportedSectorFamilyBoundary
  field
    sectorEndpointTransportAutomaticallyProvidesAggregation : Bool
    sectorEndpointTransportAutomaticallyProvidesAggregationIsFalse :
      sectorEndpointTransportAutomaticallyProvidesAggregation ≡ false

    transportedSectorFamilyPlusAggregationBuildsQFTProducer : Bool
    transportedSectorFamilyPlusAggregationBuildsQFTProducerIsTrue :
      transportedSectorFamilyPlusAggregationBuildsQFTProducer ≡ true

canonicalTransportedSectorFamilyBoundary : TransportedSectorFamilyBoundary
canonicalTransportedSectorFamilyBoundary =
  transportedSectorFamilyBoundary false refl true refl
