module DASHI.Governance.OccupyHoldoutPromotionGateRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyHoldoutPromotionGateExact as Gate

holdoutPreserved : Gate.protectedHoldoutRemainsUnread Gate.canonicalHoldoutPromotionBoundary ≡ true
holdoutPreserved = refl

noDurationModelPromoted : Gate.durationModelPromotedToProspectiveEvaluation Gate.canonicalHoldoutPromotionBoundary ≡ false
noDurationModelPromoted = refl

noBurdenEffectPromoted : Gate.coordinationBurdenEffectPromoted Gate.canonicalHoldoutPromotionBoundary ≡ false
noBurdenEffectPromoted = refl

failedDevelopmentGateBlocksHoldout : Gate.failedDevelopmentGateBlocksHoldoutConsumption Gate.canonicalHoldoutPromotionBoundary ≡ true
failedDevelopmentGateBlocksHoldout = refl
