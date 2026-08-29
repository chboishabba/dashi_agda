module DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Balaban

------------------------------------------------------------------------
-- BIDI frontier: use the literal beta-driven Balaban effective-density flow as
-- the QFT-side producer for the common-action variation theorem.
--
-- Cross-pollination with live YM PR #635 sharpens an important distinction:
-- CMP109 Eq.(5.1) / Round103 controls a physical gauge-background B-Hessian,
-- not the spacetime metric variation defining stress-energy.  Therefore the
-- metric variation below remains a separate physical theorem even when the
-- Round103 differentiated carrier is available.
------------------------------------------------------------------------

record BalabanQFTVariationReceipt
    {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaDensity.BetaDrivenCompleteDensityInputs {trajectory} {split})
    : Set₁ where
  field
    theorem1 :
      Balaban.Balaban1989Theorem1Witness
        (BetaDensity.betaDrivenCompleteDensityFlow inputs)

    scaleFor : Weld.Candidate U → Weld.Regime U → Nat

    -- This is specifically the metric/source variation needed by the QFT/GR
    -- weld.  It must not be instantiated merely by the CMP109 B-Hessian.
    metricVariationOfDensity :
      BetaDensity.Density inputs → Weld.SharedStressEnergy U

    commonVariationIsBalabanDensityVariation :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Variation.effectiveSourceVariation variation
        (Weld.coarseGrain U candidate regime) regime
      ≡
      metricVariationOfDensity
        (Balaban.densityAt
          (BetaDensity.betaDrivenCompleteDensityFlow inputs)
          (scaleFor candidate regime))

    balabanDensityVariationIsTotalQFTStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      metricVariationOfDensity
        (Balaban.densityAt
          (BetaDensity.betaDrivenCompleteDensityFlow inputs)
          (scaleFor candidate regime))
      ≡
      Weld.qftTotalStressShared U
        (Weld.coarseGrain U candidate regime)

    literalQFTStressAggregates : ∀ candidate →
      Weld.QFTStressAggregation U candidate
        (Weld.actualQFTSectorStressShared U candidate)
        (Weld.qftTotalStressShared U candidate)

open BalabanQFTVariationReceipt public

balabanReceiptBuildsQFTVariationIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaDensity.BetaDrivenCompleteDensityInputs {trajectory} {split}) →
  BalabanQFTVariationReceipt variation inputs →
  Variation.QFTVariationIdentification variation
balabanReceiptBuildsQFTVariationIdentification variation inputs receipt = record
  { Variation.QFTVariationIdentification.literalQFTStressAggregates =
      literalQFTStressAggregates receipt
  ; Variation.QFTVariationIdentification.variationEqualsTotalQFTStress =
      λ candidate regime qftAtRegime →
        trans
          (commonVariationIsBalabanDensityVariation
            receipt candidate regime qftAtRegime)
          (balabanDensityVariationIsTotalQFTStress
            receipt candidate regime qftAtRegime)
  }

balabanSection2FormAvailable :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (receipt : BalabanQFTVariationReceipt variation inputs) scale →
  Balaban.InSection2DensityClass
    (BetaDensity.betaDrivenCompleteDensityFlow inputs)
    scale
    (Balaban.densityAt (BetaDensity.betaDrivenCompleteDensityFlow inputs) scale)
balabanSection2FormAvailable receipt scale =
  Balaban.effectiveDensitiesPreserveSection2Form (theorem1 receipt) scale

balabanSection2BoundsAvailable :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (receipt : BalabanQFTVariationReceipt variation inputs) scale →
  Balaban.Section2ConditionsAndBounds
    (BetaDensity.betaDrivenCompleteDensityFlow inputs)
    scale
    (Balaban.densityAt (BetaDensity.betaDrivenCompleteDensityFlow inputs) scale)
balabanSection2BoundsAvailable receipt scale =
  Balaban.effectiveDensitiesSatisfySection2Bounds (theorem1 receipt) scale

record BalabanCommonVariationBoundary : Set where
  constructor balabanCommonVariationBoundary
  field
    section2BoundsAloneDefineMetricVariation : Bool
    section2BoundsAloneDefineMetricVariationIsFalse :
      section2BoundsAloneDefineMetricVariation ≡ false

    betaCouplingIdentityAloneDefinesStressTensor : Bool
    betaCouplingIdentityAloneDefinesStressTensorIsFalse :
      betaCouplingIdentityAloneDefinesStressTensor ≡ false

    cmp109BackgroundHessianIsMetricVariation : Bool
    cmp109BackgroundHessianIsMetricVariationIsFalse :
      cmp109BackgroundHessianIsMetricVariation ≡ false

    backgroundHessianTransportMayDropSubstitutionCurvature : Bool
    backgroundHessianTransportMayDropSubstitutionCurvatureIsFalse :
      backgroundHessianTransportMayDropSubstitutionCurvature ≡ false

    oneGaugeSectorStressIsTotalQFTStress : Bool
    oneGaugeSectorStressIsTotalQFTStressIsFalse :
      oneGaugeSectorStressIsTotalQFTStress ≡ false

    exactDensityVariationIdentificationsFeedCommonQFTReceipt : Bool
    exactDensityVariationIdentificationsFeedCommonQFTReceiptIsTrue :
      exactDensityVariationIdentificationsFeedCommonQFTReceipt ≡ true

canonicalBalabanCommonVariationBoundary : BalabanCommonVariationBoundary
canonicalBalabanCommonVariationBoundary =
  balabanCommonVariationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
