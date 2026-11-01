module DASHI.Analysis.RiemannAristotleTwoZeroUniversalRHBoundaryRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleTwoZeroUniversalRHBoundary as B

twoZeroUsefulLocally :
  B.TwoZeroUniversalBoundary.inhabitedTwoZeroTheoremUsefulLocally
    B.canonicalTwoZeroUniversalBoundary ≡ true
twoZeroUsefulLocally = refl

oneOffLineDoesNotManufactureTriple :
  B.TwoZeroUniversalBoundary.oneOffLineWitnessAutomaticallySuppliesTwoSmallerPositiveZeroHeights
    B.canonicalTwoZeroUniversalBoundary ≡ false
oneOffLineDoesNotManufactureTriple = refl

twoZeroDoesNotAloneCloseRH :
  B.TwoZeroUniversalBoundary.twoZeroTheoremAloneClosesUniversalRHBridge
    B.canonicalTwoZeroUniversalBoundary ≡ false
twoZeroDoesNotAloneCloseRH = refl

deterministicNuisanceQuotientPreferred :
  B.TwoZeroUniversalBoundary.deterministicNuisanceQuotientPreferredForUniversalLane
    B.canonicalTwoZeroUniversalBoundary ≡ true
deterministicNuisanceQuotientPreferred = refl
