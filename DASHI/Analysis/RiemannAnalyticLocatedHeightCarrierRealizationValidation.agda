module DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationValidation where

open import Data.Sum using (_⊎_)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located

minimalLocatedCarrierCoversEveryAnalyticZero :
  ∀ {analytic heightCarrier}
    (attachment :
      Located.AnalyticLocatedHeightCarrierAttachment analytic heightCarrier)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  Located.LocatedVerifiedRegion attachment rho
    ⊎ Located.LocatedHighRegion attachment rho
minimalLocatedCarrierCoversEveryAnalyticZero =
  Located.locatedVerifiedOrHigh
