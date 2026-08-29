module DASHI.Analysis.RiemannAristotleCurrentFrontierRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact as F

oneZeroClosed :
  F.AristotleCurrentFrontier.oneZeroEndpointClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
oneZeroClosed = refl

twoZeroClosed :
  F.AristotleCurrentFrontier.inhabitedTwoZeroThreeTaperClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
twoZeroClosed = refl

selectedDebtRetired :
  F.AristotleCurrentFrontier.selectedTwoZeroResidualDebtRequired
    F.canonicalAristotleCurrentFrontier ≡ false
selectedDebtRetired = refl

twoZeroUniversalWitnessesStillOpen :
  F.AristotleCurrentFrontier.twoZeroUniversalWitnessProductionClosed
    F.canonicalAristotleCurrentFrontier ≡ false
twoZeroUniversalWitnessesStillOpen = refl

poleQuotientTransversalityStillOpen :
  F.AristotleCurrentFrontier.literalPoleQuotientTransversalityClosed
    F.canonicalAristotleCurrentFrontier ≡ false
poleQuotientTransversalityStillOpen = refl

unselectedZeroTailStillOpen :
  F.AristotleCurrentFrontier.projectedUnselectedZeroTailClosed
    F.canonicalAristotleCurrentFrontier ≡ false
unselectedZeroTailStillOpen = refl

primeGammaTailStillOpen :
  F.AristotleCurrentFrontier.projectedPrimeGammaTailClosed
    F.canonicalAristotleCurrentFrontier ≡ false
primeGammaTailStillOpen = refl

farTailCompositionStillOpen :
  F.AristotleCurrentFrontier.literalFarTailCompositionClosed
    F.canonicalAristotleCurrentFrontier ≡ false
farTailCompositionStillOpen = refl

equalHeightDegeneracyStillVisible :
  F.AristotleCurrentFrontier.equalHeightDegeneracyRemoved
    F.canonicalAristotleCurrentFrontier ≡ false
equalHeightDegeneracyStillVisible = refl

rhStillOpen :
  F.AristotleCurrentFrontier.finalRHImplicationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
rhStillOpen = refl
