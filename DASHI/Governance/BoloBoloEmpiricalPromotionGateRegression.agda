module DASHI.Governance.BoloBoloEmpiricalPromotionGateRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloEmpiricalPromotionGateExact as Gate

singleBoundSetNotEnough :
  Gate.singleTargetBoundSetAutomaticallyEstablishesValidatedAdvantage Gate.canonicalEmpiricalPromotionBoundary ≡ false
singleBoundSetNotEnough = refl

robustLossCanFalsify :
  Gate.validatedRobustLossCanFalsifyCoordinationAdvantage Gate.canonicalEmpiricalPromotionBoundary ≡ true
robustLossCanFalsify = refl

sensitivityRequired :
  Gate.sensitivityAnalysisRequiredForValidatedComparison Gate.canonicalEmpiricalPromotionBoundary ≡ true
sensitivityRequired = refl

prospectiveValidationRequired :
  Gate.prospectiveValidationOrReplicationRequired Gate.canonicalEmpiricalPromotionBoundary ≡ true
prospectiveValidationRequired = refl

coordinationAdvantageNotLegitimacy :
  Gate.validatedCoordinationAdvantageCreatesPoliticalLegitimacy Gate.canonicalEmpiricalPromotionBoundary ≡ false
coordinationAdvantageNotLegitimacy = refl
