module DASHI.Physics.Foundations.CommonActionQFTGRVariationCompilerExact where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact as EinsteinVariation
import DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact as BalabanVariation
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity

------------------------------------------------------------------------
-- Final BIDI stress compiler.
--
-- GR side:
--   common metric variation = Einstein tensor
--   + literal field equation G = T
--   -> common variation = literal GR source.
--
-- QFT side:
--   common variation = metric variation of the SAME beta-driven Balaban density
--   + density variation = total QFT stress
--   + exact sector aggregation
--   -> common variation = literal total QFT source.
--
-- The generic common-action compiler then proves the QFT/GR stress weld.
------------------------------------------------------------------------

commonEinsteinAndBalabanVariationImpliesStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaDensity.BetaDrivenCompleteDensityInputs {trajectory} {split}) →
  EinsteinVariation.EinsteinTensorVariationReceipt variation →
  BalabanVariation.BalabanQFTVariationReceipt variation inputs →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
commonEinsteinAndBalabanVariationImpliesStressWeld
    variation inputs einsteinReceipt balabanReceipt token =
  Variation.commonVariationImpliesStressWeld
    variation
    (EinsteinVariation.einsteinTensorVariationBuildsGRIdentification
      variation einsteinReceipt)
    (BalabanVariation.balabanReceiptBuildsQFTVariationIdentification
      variation inputs balabanReceipt)
    token

------------------------------------------------------------------------
-- Frontier classification: after this compiler, no additional cross-sector
-- stress equality is required.  Remaining work is exactly the two variational
-- identifications plus the QFT aggregation/continuum authority carried by the
-- Balaban receipt.
------------------------------------------------------------------------

record CommonActionQFTGRCompilerBoundary : Set where
  constructor commonActionQFTGRCompilerBoundary
  field
    separateExtraStressWeldTheoremStillNeededAfterBothReceipts : Bool
    separateExtraStressWeldTheoremStillNeededAfterBothReceiptsIsFalse :
      separateExtraStressWeldTheoremStillNeededAfterBothReceipts ≡ false

    einsteinAndBalabanVariationReceiptsCompileDirectly : Bool
    einsteinAndBalabanVariationReceiptsCompileDirectlyIsTrue :
      einsteinAndBalabanVariationReceiptsCompileDirectly ≡ true

canonicalCommonActionQFTGRCompilerBoundary : CommonActionQFTGRCompilerBoundary
canonicalCommonActionQFTGRCompilerBoundary =
  commonActionQFTGRCompilerBoundary false refl true refl
