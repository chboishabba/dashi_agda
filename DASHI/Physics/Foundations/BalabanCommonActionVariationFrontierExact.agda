module DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Balaban

record BalabanSectorFlow
    {U : Weld.UnifiedCandidate}
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    trajectory : Flow.SourceNormalizedCouplingTrajectory
    split : Split.FiniteLatticeBetaSplit trajectory
    inputs : BetaDensity.BetaDrivenCompleteDensityInputs {trajectory} {split}
    theorem1 :
      Balaban.Balaban1989Theorem1Witness
        (BetaDensity.betaDrivenCompleteDensityFlow inputs)
open BalabanSectorFlow public

record BalabanSectorMetricVariation
    {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (MetricPerturbation VariationScalar : Set)
    (pairing : Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    sectorFlow : BalabanSectorFlow group

    AdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    densityMetricFirstVariation :
      BetaDensity.Density (inputs sectorFlow) →
      MetricPerturbation → VariationScalar

    finiteStressShared : Nat → Weld.SharedStressEnergy U

    finiteVariationRepresentedByFiniteStress :
      ∀ candidate regime scale perturbation →
      AdmissibleMetricPerturbation candidate regime perturbation →
      densityMetricFirstVariation
        (Balaban.densityAt
          (BetaDensity.betaDrivenCompleteDensityFlow (inputs sectorFlow)) scale)
        perturbation
      ≡ pairing (finiteStressShared scale) perturbation

    ConvergesTo : (Nat → VariationScalar) → VariationScalar → Set

    convergenceCongruent :
      ∀ left right limit →
      (∀ scale → left scale ≡ right scale) →
      ConvergesTo left limit →
      ConvergesTo right limit

    limitUnique :
      ∀ sequence leftLimit rightLimit →
      ConvergesTo sequence leftLimit →
      ConvergesTo sequence rightLimit →
      leftLimit ≡ rightLimit

    continuumFirstVariation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → VariationScalar

    finiteFirstVariationConverges :
      ∀ candidate regime perturbation →
      Weld.qftRegime U regime →
      AdmissibleMetricPerturbation candidate regime perturbation →
      ConvergesTo
        (λ scale →
          densityMetricFirstVariation
            (Balaban.densityAt
              (BetaDensity.betaDrivenCompleteDensityFlow (inputs sectorFlow)) scale)
            perturbation)
        (continuumFirstVariation candidate regime perturbation)

    finiteStressPairingConvergesToLiteralContinuumStress :
      ∀ candidate regime perturbation →
      Weld.qftRegime U regime →
      AdmissibleMetricPerturbation candidate regime perturbation →
      ConvergesTo
        (λ scale → pairing (finiteStressShared scale) perturbation)
        (pairing
          (Weld.actualQFTSectorStressShared U
            (Weld.coarseGrain U candidate regime) group)
          perturbation)
open BalabanSectorMetricVariation public

balabanSectorContinuumFirstVariationIsLiteralStressPairing :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    {MetricPerturbation VariationScalar}
    {pairing : Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)}
    (sector : BalabanSectorMetricVariation
      variation MetricPerturbation VariationScalar pairing group)
    candidate regime perturbation →
  Weld.qftRegime U regime →
  AdmissibleMetricPerturbation sector candidate regime perturbation →
  continuumFirstVariation sector candidate regime perturbation
  ≡ pairing
      (Weld.actualQFTSectorStressShared U
        (Weld.coarseGrain U candidate regime) group)
      perturbation
balabanSectorContinuumFirstVariationIsLiteralStressPairing
    sector candidate regime perturbation qftAtRegime admissible =
  let
    variationSequence = λ scale →
      densityMetricFirstVariation sector
        (Balaban.densityAt
          (BetaDensity.betaDrivenCompleteDensityFlow
            (inputs (sectorFlow sector))) scale)
        perturbation
    stressSequence = λ scale →
      pairing (finiteStressShared sector scale) perturbation
    pointwise = λ scale →
      finiteVariationRepresentedByFiniteStress
        sector candidate regime scale perturbation admissible
    variationLimit =
      finiteFirstVariationConverges
        sector candidate regime perturbation qftAtRegime admissible
    stressLimitOnVariationSequence =
      convergenceCongruent sector
        stressSequence variationSequence
        (pairing
          (Weld.actualQFTSectorStressShared U
            (Weld.coarseGrain U candidate regime) group)
          perturbation)
        (λ scale → sym (pointwise scale))
        (finiteStressPairingConvergesToLiteralContinuumStress
          sector candidate regime perturbation qftAtRegime admissible)
  in
  limitUnique sector variationSequence
    (continuumFirstVariation sector candidate regime perturbation)
    (pairing
      (Weld.actualQFTSectorStressShared U
        (Weld.coarseGrain U candidate regime) group)
      perturbation)
    variationLimit stressLimitOnVariationSequence

record BalabanAllSectorVariationReceipt
    {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) : Set₁ where
  field
    MetricPerturbation VariationScalar : Set

    stressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    sectorVariation :
      (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
      BalabanSectorMetricVariation
        variation MetricPerturbation VariationScalar stressMetricPairing group

    CommonAdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    commonAdmissibleImpliesSectorAdmissible :
      ∀ group candidate regime perturbation →
      CommonAdmissibleMetricPerturbation candidate regime perturbation →
      AdmissibleMetricPerturbation (sectorVariation group)
        candidate regime perturbation

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
      aggregateSectorStress (Weld.actualQFTSectorStressShared U candidate)
      ≡ Weld.qftTotalStressShared U candidate

    literalQFTStressAggregates : ∀ candidate →
      Weld.QFTStressAggregation U candidate
        (Weld.actualQFTSectorStressShared U candidate)
        (Weld.qftTotalStressShared U candidate)
open BalabanAllSectorVariationReceipt public

balabanSectorFirstVariationIsLiteralStressPairing :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (receipt : BalabanAllSectorVariationReceipt variation)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    candidate regime perturbation →
  Weld.qftRegime U regime →
  CommonAdmissibleMetricPerturbation receipt candidate regime perturbation →
  continuumFirstVariation (sectorVariation receipt group)
    candidate regime perturbation
  ≡ stressMetricPairing receipt
      (Weld.actualQFTSectorStressShared U
        (Weld.coarseGrain U candidate regime) group)
      perturbation
balabanSectorFirstVariationIsLiteralStressPairing
    variation receipt group candidate regime perturbation qftAtRegime commonAdmissible =
  balabanSectorContinuumFirstVariationIsLiteralStressPairing
    (sectorVariation receipt group)
    candidate regime perturbation qftAtRegime
    (commonAdmissibleImpliesSectorAdmissible
      receipt group candidate regime perturbation commonAdmissible)

balabanAggregateSectorVariationIsAggregateStressPairing :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (receipt : BalabanAllSectorVariationReceipt variation)
    candidate regime perturbation →
  Weld.qftRegime U regime →
  CommonAdmissibleMetricPerturbation receipt candidate regime perturbation →
  aggregateVariationScalars receipt
    (λ group → continuumFirstVariation (sectorVariation receipt group)
      candidate regime perturbation)
  ≡ stressMetricPairing receipt
      (aggregateSectorStress receipt
        (Weld.actualQFTSectorStressShared U
          (Weld.coarseGrain U candidate regime)))
      perturbation
balabanAggregateSectorVariationIsAggregateStressPairing
    variation receipt candidate regime perturbation qftAtRegime commonAdmissible =
  trans
    (aggregateVariationScalarsCongruent receipt _ _
      (λ group →
        balabanSectorFirstVariationIsLiteralStressPairing
          variation receipt group candidate regime perturbation
          qftAtRegime commonAdmissible))
    (sym (aggregateStressPairingCommutes receipt
      (Weld.coarseGrain U candidate regime) perturbation))

balabanSectorFamilyBuildsQFTVariationIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  BalabanAllSectorVariationReceipt variation →
  Variation.QFTVariationIdentification variation
balabanSectorFamilyBuildsQFTVariationIdentification variation receipt = record
  { Variation.QFTVariationIdentification.literalQFTStressAggregates =
      literalQFTStressAggregates receipt
  ; Variation.QFTVariationIdentification.variationEqualsTotalQFTStress =
      λ candidate regime qftAtRegime →
        trans
          (commonVariationIsAggregateLiteralSectorStress
            receipt candidate regime qftAtRegime)
          (aggregateLiteralSectorStressIsDeclaredTotal
            receipt (Weld.coarseGrain U candidate regime))
  }

balabanSectorSection2FormAvailable :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    (receipt : BalabanAllSectorVariationReceipt variation)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) scale →
  let sector = sectorVariation receipt group
      flow = sectorFlow sector
  in Balaban.InSection2DensityClass
      (BetaDensity.betaDrivenCompleteDensityFlow (inputs flow))
      scale
      (Balaban.densityAt
        (BetaDensity.betaDrivenCompleteDensityFlow (inputs flow)) scale)
balabanSectorSection2FormAvailable receipt group scale =
  let sector = sectorVariation receipt group
      flow = sectorFlow sector
  in Balaban.effectiveDensitiesPreserveSection2Form (theorem1 flow) scale

record BalabanCommonVariationBoundary : Set where
  constructor balabanCommonVariationBoundary
  field
    finiteBalabanDensityVariationIsLiteralContinuumStressWithoutLimit : Bool
    finiteBalabanDensityVariationIsLiteralContinuumStressWithoutLimitIsFalse :
      finiteBalabanDensityVariationIsLiteralContinuumStressWithoutLimit ≡ false

    measureContinuumLimitAloneCommutesWithMetricVariation : Bool
    measureContinuumLimitAloneCommutesWithMetricVariationIsFalse :
      measureContinuumLimitAloneCommutesWithMetricVariation ≡ false

    metricVariationFunctionalIsStressTensorWithoutPairing : Bool
    metricVariationFunctionalIsStressTensorWithoutPairingIsFalse :
      metricVariationFunctionalIsStressTensorWithoutPairing ≡ false

    sectorSpecificMetricLanguagesAutomaticallyDefineOneGravitatingMetric : Bool
    sectorSpecificMetricLanguagesAutomaticallyDefineOneGravitatingMetricIsFalse :
      sectorSpecificMetricLanguagesAutomaticallyDefineOneGravitatingMetric ≡ false

    tensorAggregationAutomaticallyCommutesWithMetricPairing : Bool
    tensorAggregationAutomaticallyCommutesWithMetricPairingIsFalse :
      tensorAggregationAutomaticallyCommutesWithMetricPairing ≡ false

    finiteRepresentationPlusCompatibleLimitsProducesContinuumSectorStress : Bool
    finiteRepresentationPlusCompatibleLimitsProducesContinuumSectorStressIsTrue :
      finiteRepresentationPlusCompatibleLimitsProducesContinuumSectorStress ≡ true

    sectorwiseContinuumVariationPlusAggregationFeedsCommonQFTReceipt : Bool
    sectorwiseContinuumVariationPlusAggregationFeedsCommonQFTReceiptIsTrue :
      sectorwiseContinuumVariationPlusAggregationFeedsCommonQFTReceipt ≡ true

canonicalBalabanCommonVariationBoundary : BalabanCommonVariationBoundary
canonicalBalabanCommonVariationBoundary =
  balabanCommonVariationBoundary
    false refl false refl false refl false refl false refl true refl true refl
