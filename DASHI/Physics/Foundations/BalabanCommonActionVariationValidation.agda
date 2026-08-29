module DASHI.Physics.Foundations.BalabanCommonActionVariationValidation where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact as BalabanVariation
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

balabanSectorFamilyProducesQFTIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  BalabanVariation.BalabanAllSectorVariationReceipt variation →
  Variation.QFTVariationIdentification variation
balabanSectorFamilyProducesQFTIdentification =
  BalabanVariation.balabanSectorFamilyBuildsQFTVariationIdentification

balabanOneSectorRemainsSectorIndexed :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (receipt : BalabanVariation.BalabanAllSectorVariationReceipt variation)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    candidate regime →
  Weld.qftRegime U regime →
  let sector = BalabanVariation.sectorVariation receipt group
  in
  BalabanVariation.metricVariationOfDensity sector
    (BalabanVariation.Balaban.densityAt
      (BalabanVariation.BetaDensity.betaDrivenCompleteDensityFlow
        (BalabanVariation.inputs (BalabanVariation.sectorFlow sector)))
      (BalabanVariation.scaleFor sector candidate regime))
  ≡
  Weld.actualQFTSectorStressShared U
    (Weld.coarseGrain U candidate regime) group
balabanOneSectorRemainsSectorIndexed =
  BalabanVariation.balabanSectorVariationIdentifiesLiteralStress
