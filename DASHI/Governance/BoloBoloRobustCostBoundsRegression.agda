module DASHI.Governance.BoloBoloRobustCostBoundsRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloRobustCostBoundsExact as Bounds

robustWinUsesWorstCaseBounds :
  Bounds.robustWinUsesRemovedLowerAndOverheadUpper Bounds.canonicalRobustCostBoundary ≡ true
robustWinUsesWorstCaseBounds = refl

robustLossUsesWorstCaseBounds :
  Bounds.robustLossUsesRemovedUpperAndOverheadLower Bounds.canonicalRobustCostBoundary ≡ true
robustLossUsesWorstCaseBounds = refl

pointEstimateNotRequired :
  Bounds.exactPointIdentificationRequiredForRobustClassification Bounds.canonicalRobustCostBoundary ≡ false
pointEstimateNotRequired = refl

overlappingBoundsMayRemainIndeterminate :
  Bounds.overlappingIntervalsMayRemainIndeterminate Bounds.canonicalRobustCostBoundary ≡ true
overlappingBoundsMayRemainIndeterminate = refl

occupyBoundsNotUniversal :
  Bounds.occupyDerivedBoundsAutomaticallyTransferToBolo Bounds.canonicalRobustCostBoundary ≡ false
occupyBoundsNotUniversal = refl

robustWinNotPoliticalLegitimacy :
  Bounds.robustCoordinationWinCreatesPoliticalLegitimacy Bounds.canonicalRobustCostBoundary ≡ false
robustWinNotPoliticalLegitimacy = refl
