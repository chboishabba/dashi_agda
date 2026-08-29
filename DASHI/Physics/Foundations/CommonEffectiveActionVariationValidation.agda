module DASHI.Physics.Foundations.CommonEffectiveActionVariationValidation where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Source
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation

variationProducesSharedSource :
  ∀ {U : Weld.UnifiedCandidate} →
  Variation.CommonEffectiveActionVariation U →
  Source.SharedEffectiveSourceTheory U
variationProducesSharedSource = Variation.variationBuildsSharedEffectiveSource

variationAndGRIdentificationProduceFactorisation :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  Variation.EinsteinVariationIdentification variation →
  Source.GRSourceFactorisation (Variation.variationBuildsSharedEffectiveSource variation)
variationAndGRIdentificationProduceFactorisation =
  Variation.variationIdentifiesGRSource

variationAndQFTIdentificationProduceFactorisation :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  Variation.QFTVariationIdentification variation →
  Source.QFTSourceFactorisation (Variation.variationBuildsSharedEffectiveSource variation)
variationAndQFTIdentificationProduceFactorisation =
  Variation.variationIdentifiesQFTSource

variationIdentificationsCloseStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  Variation.EinsteinVariationIdentification variation →
  Variation.QFTVariationIdentification variation →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
variationIdentificationsCloseStressWeld =
  Variation.commonVariationImpliesStressWeld
