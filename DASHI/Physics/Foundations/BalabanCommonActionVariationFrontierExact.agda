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
-- Therefore one beta-driven density must first identify ONE literal sector
-- stress tensor.  Only a family of such sector receipts plus an explicit
-- aggregation theorem may feed the total QFT stress consumed by the QFT/GR
-- weld.
--
-- Separately, CMP109 Round103 controls a gauge-background B-Hessian.  That is
-- not the spacetime metric variation defining stress-energy without an explicit
-- transport theorem.
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

    metricVariationOfDensity :
      BetaDensity.Density (inputs sectorFlow) → Weld.SharedStressEnergy U

    -- Literal pure-YM sector statement.  This is the physical theorem leaf:
    -- metric variation of the SAME beta-driven density equals the literal
    -- group-indexed stress tensor already carried by the QFT construction.
    densityMetricVariationIsLiteralSectorStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      metricVariationOfDensity
        (Balaban.densityAt
          (BetaDensity.betaDrivenCompleteDensityFlow (inputs sectorFlow))
          (scaleFor candidate regime))
      ≡
      Weld.actualQFTSectorStressShared U
        (Weld.coarseGrain U candidate regime) group

open BalabanSectorMetricVariation public

record BalabanAllSectorVariationReceipt
    {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) : Set₁ where
  field
    sectorVariation :
      (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
      BalabanSectorMetricVariation variation group

    -- Application-owned aggregation operation on the shared stress carrier.
    aggregateSectorStress :
      (QFT.CompactSimpleGroup (Weld.qftCarriers U) → Weld.SharedStressEnergy U) →
      Weld.SharedStressEnergy U

    -- The common effective-source variation is the aggregate of the literal
    -- sector stresses on the SAME coarse-grained candidate.
    commonVariationIsAggregateLiteralSectorStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Variation.effectiveSourceVariation variation
        (Weld.coarseGrain U candidate regime) regime
      ≡
      aggregateSectorStress
        (Weld.actualQFTSectorStressShared U
          (Weld.coarseGrain U candidate regime))

    -- That aggregate is exactly the total QFT stress already declared by the
    -- unified candidate.  No one pure-YM sector is promoted to the total.
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
-- Sectorwise Bałaban provenance is exposed independently of total aggregation.
------------------------------------------------------------------------

balabanSectorVariationIdentifiesLiteralStress :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (receipt : BalabanAllSectorVariationReceipt variation)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    candidate regime →
  Weld.qftRegime U regime →
  let sector = sectorVariation receipt group
  in
  metricVariationOfDensity sector
    (Balaban.densityAt
      (BetaDensity.betaDrivenCompleteDensityFlow
        (inputs (sectorFlow sector)))
      (scaleFor sector candidate regime))
  ≡
  Weld.actualQFTSectorStressShared U
    (Weld.coarseGrain U candidate regime) group
balabanSectorVariationIdentifiesLiteralStress variation receipt group candidate regime =
  densityMetricVariationIsLiteralSectorStress
    (sectorVariation receipt group) candidate regime

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

------------------------------------------------------------------------
-- Existing source authority still supplies Section-2 form/bounds sectorwise.
------------------------------------------------------------------------

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

    backgroundHessianTransportMayDropSubstitutionCurvature : Bool
    backgroundHessianTransportMayDropSubstitutionCurvatureIsFalse :
      backgroundHessianTransportMayDropSubstitutionCurvature ≡ false

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
