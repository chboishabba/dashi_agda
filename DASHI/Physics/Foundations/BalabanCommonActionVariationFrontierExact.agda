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
-- Existing machine-checked producer:
--   beta history -> literal effective-density flow, with the same coupling
--   trajectory and conditional CMP122 Section-2 preservation/bounds.
--
-- Missing physical analysis:
--   metric variation of that SAME density -> total QFT stress-energy.
--
-- This module makes that missing theorem exact and proves that, once supplied,
-- it constructs `QFTVariationIdentification` for the common-action compiler.
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

    -- Applications identify each candidate/regime pair with the literal RG
    -- scale whose density is being varied.  This prevents a parallel-flow
    -- substitution at the final QFT weld.
    scaleFor : Weld.Candidate U → Weld.Regime U → Nat

    metricVariationOfDensity :
      BetaDensity.Density inputs → Weld.SharedStressEnergy U

    -- The common effective-source variation is literally the metric variation
    -- of the density from the beta-driven Balaban flow at the selected scale.
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

    -- The same density variation is the TOTAL QFT stress-energy, not merely one
    -- compact-simple gauge-sector stress tensor.
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

------------------------------------------------------------------------
-- Compiler: once the two genuine variational identifications are proved on the
-- same beta-driven density flow, the generic common-action QFT identification
-- follows by equality transitivity.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Existing source authority supplies density-class preservation and bounds on
-- the exact flow, but not the metric derivative.  These helper theorems expose
-- that distinction explicitly.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Honest frontier classification.
------------------------------------------------------------------------

record BalabanCommonVariationBoundary : Set where
  constructor balabanCommonVariationBoundary
  field
    section2BoundsAloneDefineMetricVariation : Bool
    section2BoundsAloneDefineMetricVariationIsFalse :
      section2BoundsAloneDefineMetricVariation ≡ false

    betaCouplingIdentityAloneDefinesStressTensor : Bool
    betaCouplingIdentityAloneDefinesStressTensorIsFalse :
      betaCouplingIdentityAloneDefinesStressTensor ≡ false

    oneGaugeSectorStressIsTotalQFTStress : Bool
    oneGaugeSectorStressIsTotalQFTStressIsFalse :
      oneGaugeSectorStressIsTotalQFTStress ≡ false

    exactDensityVariationIdentificationsFeedCommonQFTReceipt : Bool
    exactDensityVariationIdentificationsFeedCommonQFTReceiptIsTrue :
      exactDensityVariationIdentificationsFeedCommonQFTReceipt ≡ true

canonicalBalabanCommonVariationBoundary : BalabanCommonVariationBoundary
canonicalBalabanCommonVariationBoundary =
  balabanCommonVariationBoundary false refl false refl false refl true refl
