module DASHI.Physics.Foundations.CommonActionQFTGRVariationCompilerExact where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact as EinsteinVariation
import DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact as BalabanVariation

------------------------------------------------------------------------
-- Final BIDI stress compiler, corrected sectorwise.
--
-- GR side:
--   common metric variation = Einstein tensor
--   + literal field equation G = T
--   -> common variation = literal GR source.
--
-- QFT side:
--   for every compact simple group G,
--     metric variation of the SAME beta-driven Balaban sector density
--       = literal sector stress T^(G)
--   + explicit aggregation of all literal sector stresses
--   + common variation = that aggregate
--   -> common variation = literal total QFT source.
--
-- No single pure-YM sector is identified with total gravitating stress.
------------------------------------------------------------------------

commonEinsteinAndBalabanVariationImpliesStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  EinsteinVariation.EinsteinTensorVariationReceipt variation →
  BalabanVariation.BalabanAllSectorVariationReceipt variation →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
commonEinsteinAndBalabanVariationImpliesStressWeld
    variation einsteinReceipt balabanReceipt token =
  Variation.commonVariationImpliesStressWeld
    variation
    (EinsteinVariation.einsteinTensorVariationBuildsGRIdentification
      variation einsteinReceipt)
    (BalabanVariation.balabanSectorFamilyBuildsQFTVariationIdentification
      variation balabanReceipt)
    token

record CommonActionQFTGRCompilerBoundary : Set where
  constructor commonActionQFTGRCompilerBoundary
  field
    separateExtraStressWeldTheoremStillNeededAfterBothReceipts : Bool
    separateExtraStressWeldTheoremStillNeededAfterBothReceiptsIsFalse :
      separateExtraStressWeldTheoremStillNeededAfterBothReceipts ≡ false

    onePureYangMillsSectorCanStandForTotalQFTStress : Bool
    onePureYangMillsSectorCanStandForTotalQFTStressIsFalse :
      onePureYangMillsSectorCanStandForTotalQFTStress ≡ false

    einsteinAndSectorwiseBalabanVariationReceiptsCompileDirectly : Bool
    einsteinAndSectorwiseBalabanVariationReceiptsCompileDirectlyIsTrue :
      einsteinAndSectorwiseBalabanVariationReceiptsCompileDirectly ≡ true

canonicalCommonActionQFTGRCompilerBoundary : CommonActionQFTGRCompilerBoundary
canonicalCommonActionQFTGRCompilerBoundary =
  commonActionQFTGRCompilerBoundary false refl false refl true refl
