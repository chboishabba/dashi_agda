module DASHI.Analysis.RiemannAnalyticCoordinateVerifiedRegionRealizationValidation where

open import Data.Sum using (_⊎_)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.RiemannAnalyticCoordinateVerifiedRegionRealizationExact as R3Star

r3StarConstructsCanonicalLowComplementCover :
  ∀ {analytic}
    (realization : R3Star.AnalyticCoordinateVerifiedRegionRealization analytic)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  Coordinate.WithinPublishedVerifiedHeight
      (R3Star.coordinate realization) rho
    ⊎ R3Star.VerifiedRegionComplementHigh realization rho
r3StarConstructsCanonicalLowComplementCover =
  R3Star.verifiedOrComplementHighCover
