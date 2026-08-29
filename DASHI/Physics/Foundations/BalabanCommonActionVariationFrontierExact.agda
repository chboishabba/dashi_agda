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
-- BIDI frontier, corrected by live YM PR #635.
--
-- Bałaban's constructive flow is a pure-YM / compact-simple-group sector.
-- Therefore one beta-driven density first identifies ONE literal sector stress
-- tensor.  Only a family of such receipts plus explicit aggregation may feed
-- total QFT stress.
--
-- A second correction is variational: the first metric variation is naturally
-- a functional of a metric perturbation h, while the stress tensor represents
-- that functional through an application-owned pairing/normalisation:
--
--   delta_g rho[h] = <T , h>.
--
-- We do not silently identify the derivative functional with a tensor carrier.
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

    -- Literal first metric variation of the beta-driven sector density.
    densityMetricFirstVariation :
      BetaDensity.Density (inputs sectorFlow) →
      MetricPerturbation → VariationScalar

    -- Explicit convention pairing between the shared stress carrier and a
    -- metric perturbation.  This is where factors such as 1/2, sqrt(|g|),
    -- index placement, Euclidean/Lorentz continuation, etc. must be owned.
    stressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    -- Physical same-object leaf for one compact-simple sector.
    densityFirstVariationRepresentedByLiteralSectorStress :
      ∀ candidate regime perturbation →
      Weld.qftRegime U regime →
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

    -- At the tensor level, the common effective source is the aggregate of the
    -- literal sector stresses on the same coarse-grained candidate.  The
    -- sector receipts above separately justify each T^(G) variationally.
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
-- Expose the literal variational identity sectorwise.
------------------------------------------------------------------------

balabanSectorFirstVariationIsLiteralStressPairing :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (receipt : BalabanAllSectorVariationReceipt variation)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    candidate regime perturbation →
  Weld.qftRegime U regime →
  let sector = sectorVariation receipt group
  in
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

------------------------------------------------------------------------
-- Compiler to the generic common-action QFT identification.
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
    true refl
