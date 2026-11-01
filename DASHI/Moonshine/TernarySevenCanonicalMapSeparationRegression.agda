module DASHI.Moonshine.TernarySevenCanonicalMapSeparationRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Moonshine.TernarySevenCanonicalMapSeparationExact as Map

lowLowRegression :
  Map.phaseSevenToShape Phase.nonUnitLowLow ≡ Shape.constantShape
lowLowRegression = refl

lowHighRegression :
  Map.phaseSevenToShape Phase.nonUnitLowHigh ≡ Shape.rank2TwoFixedShape
lowHighRegression = refl

midLowCollisionRegression :
  Map.phaseSevenToShape Phase.nonUnitLowHigh
  ≡ Map.phaseSevenToShape Phase.nonUnitMidLow
midLowCollisionRegression = refl

identityExcludedRegression :
  Map.phaseSevenToShape Phase.nonUnitLowLow ≡ Shape.identityShape → ⊥
identityExcludedRegression = Map.identityNotInPhaseSevenImage Phase.nonUnitLowLow

canonicalMapNotBijectiveByCardinality :
  Map.TernarySevenCanonicalMapBoundary.equalSevenCardinalityCreatesNaturalBijection
    Map.canonicalTernarySevenCanonicalMapBoundary
  ≡ false
canonicalMapNotBijectiveByCardinality = refl

canonicalImageIsThreeShapeClasses :
  Map.TernarySevenCanonicalMapBoundary.canonicalImageHasThreeShapeClasses
    Map.canonicalTernarySevenCanonicalMapBoundary
  ≡ true
canonicalImageIsThreeShapeClasses = refl
