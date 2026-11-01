module DASHI.Physics.Foundations.EinsteinCommonActionVariationValidation where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact as EinsteinVariation

commonVariationToEinsteinBuildsGRIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  EinsteinVariation.EinsteinTensorVariationReceipt variation →
  Variation.EinsteinVariationIdentification variation
commonVariationToEinsteinBuildsGRIdentification =
  EinsteinVariation.einsteinTensorVariationBuildsGRIdentification
