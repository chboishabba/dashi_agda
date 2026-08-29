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
-- For each compact-simple pure-YM sector:
--   * one beta-driven density flow is fixed;
--   * one admitted metric-perturbation fibre is declared;
--   * the first metric variation is represented by the literal sector stress
--     through an explicit pairing convention on that admitted fibre.
--
-- Only after every sector is so identified does an explicit aggregation theorem
-- produce the total QFT stress consumed by the QFT/GR weld.
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
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    sectorFlow : BalabanSectorFlow group

    scaleFor : Weld.Candidate U → Weld.Regime U → Nat

    MetricPerturbation : Set
    VariationScalar : Set

    -- Consumer-facing image of the canonical CMP116 metric/source analytic
    -- domain.  The YM producer branch proves how this fibre sits inside its
    -- literal source-coordinate ball; Foundations only consumes membership.
    AdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    densityMetricFirstVariation :
      BetaDensity.Density (inputs sectorFlow) →
      MetricPerturbation → VariationScalar

    stressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

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
    sectorVariation :
      (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
      BalabanSectorMetricVariation variation group

    aggregateSectorStress :
      (QFT.CompactSimpleGroup (Weld.qftCarriers U) → Weld.SharedStressEnergy U) →
      Weld.SharedStressEnergy U

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

balabanSectorFirstVariationIsLiteralStressPairing :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (receipt : BalabanAllSectorVariationReceipt variation)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    candidate regime perturbation →
  Weld.qftRegime U regime →
  let sector = sectorVariation receipt group
  in
  AdmissibleMetricPerturbation sector candidate regime perturbation →
  densityMetricFirstVariation sector
    (Balaban.densityAt
      (BetaDensity.betaDrivenCompleteDensityFlow
        (inputs (sectorFlow sector)))
      (scaleFor sector candidate regime))
    perturbation
  ≡
  stressMetricPairing sector
    (Weld.actualQFTSectorStressShared U
      (Weld.coarseGrain U candidate regime) group)
    perturbation
balabanSectorFirstVariationIsLiteralStressPairing
    variation receipt group candidate regime perturbation =
  densityFirstVariationRepresentedByLiteralSectorStress
    (sectorVariation receipt group) candidate regime perturbation

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

    stressRepresentationAutomaticallyHoldsOutsideAdmittedMetricDomain : Bool
    stressRepresentationAutomaticallyHoldsOutsideAdmittedMetricDomainIsFalse :
      stressRepresentationAutomaticallyHoldsOutsideAdmittedMetricDomain ≡ false

    oneBalabanPureGaugeDensityIsTotalQFTStress : Bool
    oneBalabanPureGaugeDensityIsTotalQFTStressIsFalse :
      oneBalabanPureGaugeDensityIsTotalQFTStress ≡ false

    oneGaugeSectorStressIsTotalQFTStress : Bool
    oneGaugeSectorStressIsTotalQFTStressIsFalse :
      oneGaugeSectorStressIsTotalQFTStress ≡ false

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
    true refl
