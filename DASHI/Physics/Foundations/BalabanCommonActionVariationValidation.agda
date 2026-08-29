module DASHI.Physics.Foundations.BalabanCommonActionVariationValidation where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact as BalabanVariation

balabanSectorFamilyProducesQFTIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  BalabanVariation.BalabanAllSectorVariationReceipt variation →
  Variation.QFTVariationIdentification variation
balabanSectorFamilyProducesQFTIdentification =
  BalabanVariation.balabanSectorFamilyBuildsQFTVariationIdentification
