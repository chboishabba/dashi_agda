module DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Balaban

------------------------------------------------------------------------
-- BIDI frontier, synchronized with live YM PR #635 Round106.
--
-- Gravity couples every QFT sector to the SAME metric perturbation.  Therefore
-- the all-sector receipt owns one MetricPerturbation carrier, one variation
-- scalar, and one stress/metric pairing convention.  Each pure-YM Balaban sector
-- must represent its first variation against that common perturbation language.
--
-- Only after those sectorwise identities are proved do explicit tensor and
-- scalar aggregation laws produce the total QFT stress functional.
------------------------------------------------------------------------

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
    (stressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    sectorFlow : BalabanSectorFlow group

    scaleFor : Weld.Candidate U → Weld.Regime U → Nat

    AdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    densityMetricFirstVariation :
      BetaDensity.Density (inputs sectorFlow) →
      MetricPerturbation → VariationScalar

    densityFirstVariationRepresentedByLiteralSectorStress :
      ∀ candidate regime perturbation →
      Weld.qftRegime U regime →
      AdmissibleMetricPerturbation candidate regime perturbation →
      densityMetricFirstVariation
        (Balaban.densityAt
          (BetaDensity.betaDrivenCompleteDensityFlow (inputs sectorFlow))
          (scaleFor candidate regime))
        perturbation
      ≡
      stressMetricPairing
        (Weld.actualQFTSectorStressShared U
          (Weld.coarseGrain U candidate regime) group)
        perturbation

open BalabanSectorMetricVariation public

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

    -- One common perturbation fibre whose members are admitted by every sector.
    CommonAdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    commonAdmissibleImpliesSectorAdmissible :
      ∀ group candidate regime perturbation →
      CommonAdmissibleMetricPerturbation candidate regime perturbation →
      AdmissibleMetricPerturbation (sectorVariation group)
        candidate regime perturbation

    -- Tensor aggregation and scalar-functional aggregation are separate data.
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

    -- Pairing with the aggregated stress is exactly aggregation of the sector
    -- pairings.  This is the linearity/normalisation theorem needed to pass from
    -- sector stress representations to the total stress functional.
    aggregateStressPairingCommutes :
      ∀ candidate perturbation →
      stressMetricPairing
        (aggregateSectorStress
          (Weld.actualQFTSectorStressShared U candidate))
        perturbation
      ≡
      aggregateVariationScalars
        (λ group →
          stressMetricPairing
            (Weld.actualQFTSectorStressShared U candidate group)
            perturbation)

    commonVariationIsAggregateLiteralSectorStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Variation.effectiveSourceVariation variation
        (Weld.coarseGrain U candidate regime) regime
      ≡
      aggregateSectorStress
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

------------------------------------------------------------------------
-- Sector and total variational identities on one common metric language.
------------------------------------------------------------------------

balabanSectorFirstVariationIsLiteralStressPairing :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (receipt : BalabanAllSectorVariationReceipt variation)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    candidate regime perturbation →
  Weld.qftRegime U regime →
  CommonAdmissibleMetricPerturbation receipt candidate regime perturbation →
  let sector = sectorVariation receipt group
  in
  densityMetricFirstVariation sector
    (Balaban.densityAt
      (BetaDensity.betaDrivenCompleteDensityFlow
        (inputs (sectorFlow sector)))
      (scaleFor sector candidate regime))
    perturbation
  ≡
  stressMetricPairing receipt
    (Weld.actualQFTSectorStressShared U
      (Weld.coarseGrain U candidate regime) group)
    perturbation
balabanSectorFirstVariationIsLiteralStressPairing
    variation receipt group candidate regime perturbation qftAtRegime commonAdmissible =
  densityFirstVariationRepresentedByLiteralSectorStress
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
    (λ group →
      let sector = sectorVariation receipt group
      in densityMetricFirstVariation sector
        (Balaban.densityAt
          (BetaDensity.betaDrivenCompleteDensityFlow
            (inputs (sectorFlow sector)))
          (scaleFor sector candidate regime))
        perturbation)
  ≡
  stressMetricPairing receipt
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

------------------------------------------------------------------------
-- Compiler to the generic tensor-valued common-action QFT identification.
------------------------------------------------------------------------

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
  in
  Balaban.InSection2DensityClass
    (BetaDensity.betaDrivenCompleteDensityFlow (inputs flow))
    scale
    (Balaban.densityAt
      (BetaDensity.betaDrivenCompleteDensityFlow (inputs flow)) scale)
balabanSectorSection2FormAvailable receipt group scale =
  let sector = sectorVariation receipt group
      flow = sectorFlow sector
  in
  Balaban.effectiveDensitiesPreserveSection2Form (theorem1 flow) scale

record BalabanCommonVariationBoundary : Set where
  constructor balabanCommonVariationBoundary
  field
    section2BoundsAloneDefineMetricVariation : Bool
    section2BoundsAloneDefineMetricVariationIsFalse :
      section2BoundsAloneDefineMetricVariation ≡ false

    cmp109BackgroundHessianIsMetricVariation : Bool
    cmp109BackgroundHessianIsMetricVariationIsFalse :
      cmp109BackgroundHessianIsMetricVariation ≡ false

    metricVariationFunctionalIsStressTensorWithoutPairing : Bool
    metricVariationFunctionalIsStressTensorWithoutPairingIsFalse :
      metricVariationFunctionalIsStressTensorWithoutPairing ≡ false

    sectorSpecificMetricLanguagesAutomaticallyDefineOneGravitatingMetric : Bool
    sectorSpecificMetricLanguagesAutomaticallyDefineOneGravitatingMetricIsFalse :
      sectorSpecificMetricLanguagesAutomaticallyDefineOneGravitatingMetric ≡ false

    stressRepresentationAutomaticallyHoldsOutsideAdmittedMetricDomain : Bool
    stressRepresentationAutomaticallyHoldsOutsideAdmittedMetricDomainIsFalse :
      stressRepresentationAutomaticallyHoldsOutsideAdmittedMetricDomain ≡ false

    tensorAggregationAutomaticallyCommutesWithMetricPairing : Bool
    tensorAggregationAutomaticallyCommutesWithMetricPairingIsFalse :
      tensorAggregationAutomaticallyCommutesWithMetricPairing ≡ false

    oneBalabanPureGaugeDensityIsTotalQFTStress : Bool
    oneBalabanPureGaugeDensityIsTotalQFTStressIsFalse :
      oneBalabanPureGaugeDensityIsTotalQFTStress ≡ false

    sectorwiseVariationPlusExactAggregationFeedsCommonQFTReceipt : Bool
    sectorwiseVariationPlusExactAggregationFeedsCommonQFTReceiptIsTrue :
      sectorwiseVariationPlusExactAggregationFeedsCommonQFTReceipt ≡ true

canonicalBalabanCommonVariationBoundary : BalabanCommonVariationBoundary
canonicalBalabanCommonVariationBoundary =
  balabanCommonVariationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
