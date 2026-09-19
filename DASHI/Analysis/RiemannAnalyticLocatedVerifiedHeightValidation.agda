module DASHI.Analysis.RiemannAnalyticLocatedVerifiedHeightValidation where

open import Data.Sum using (_⊎_)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAnalyticLocatedVerifiedHeightExact as Located

locatedSplitCoversEveryAnalyticZero :
  ∀ {analytic realPackage}
    (attachment :
      Located.AnalyticConstructiveRealCarrierAttachment analytic realPackage)
    (window : Located.RationalLocatedHeightWindow realPackage)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  Located.LocatedVerifiedRegion attachment window rho
    ⊎ Located.LocatedHighRegion attachment window rho
locatedSplitCoversEveryAnalyticZero =
  Located.locatedVerifiedOrHigh
