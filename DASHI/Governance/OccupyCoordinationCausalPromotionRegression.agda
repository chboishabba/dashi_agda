module DASHI.Governance.OccupyCoordinationCausalPromotionRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyCoordinationCausalPromotionExact as Causal

causalGraphRequired :
  Causal.requiresDeclaredCausalGraph Causal.canonicalCausalPromotionRequirements ≡ true
causalGraphRequired = refl

identificationRequired :
  Causal.requiresIdentificationCriterion Causal.canonicalCausalPromotionRequirements ≡ true
identificationRequired = refl

confoundBoundaryRequired :
  Causal.requiresConfoundSelectionBoundary Causal.canonicalCausalPromotionRequirements ≡ true
confoundBoundaryRequired = refl

estimandMapRequired :
  Causal.requiresEstimandObservableMap Causal.canonicalCausalPromotionRequirements ≡ true
estimandMapRequired = refl

sensitivityRequired :
  Causal.requiresSensitivityAnalysis Causal.canonicalCausalPromotionRequirements ≡ true
sensitivityRequired = refl

causalPromotionStillBlocked :
  Causal.incidenceBurdenCausalEffectPromoted Causal.canonicalCausalPromotionBoundary ≡ false
causalPromotionStillBlocked = refl
