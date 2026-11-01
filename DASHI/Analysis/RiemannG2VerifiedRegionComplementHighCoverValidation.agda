module DASHI.Analysis.RiemannG2VerifiedRegionComplementHighCoverValidation where

open import Data.Sum using (_⊎_)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.RiemannG2VerifiedRegionComplementHighCoverExact as R4

complementPartitionCoversEveryZero :
  ∀ {analytic}
    (coordinate : Coordinate.AnalyticCoordinateTerminalRefinement analytic)
    (decidable : R4.DecidablePublishedVerifiedRegion coordinate)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  Coordinate.WithinPublishedVerifiedHeight coordinate rho
    ⊎ R4.VerifiedRegionComplementHigh coordinate rho
complementPartitionCoversEveryZero =
  R4.verifiedOrComplementHighCover
