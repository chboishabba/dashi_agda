module DASHI.Moonshine.TernarySevenCanonicalMapSeparationExact where

------------------------------------------------------------------------
-- CANONICAL MAP BETWEEN TWO EXISTING "SEVEN" CARRIERS
--
-- Existing surfaces:
--   * TernaryEndomorphismPhaseQuotientExact has seven nonunit classes inside
--     the normalized phase quotient 9 = 2 + 7;
--   * TernaryEndomorphismConjugacyExact has seven S3-conjugacy functional-
--     graph shapes on the full 27 endomorphism carrier.
--
-- Equal cardinality alone does not identify these sevens.  There is, however,
-- a canonical structure-derived map: take the phase-normalized representative
-- with low-input output fixed to tri-low, then classify its functional-graph
-- shape.  This module computes that map exactly.
--
-- Result: the canonical 7 -> 7 map is highly non-injective and its image has
-- only three shape classes.  Thus the two seven-state carriers are not related
-- by the naive bijection suggested by cardinality coincidence.
--
-- Source context:
--   John D. Dixon and Brian Mortimer, "Permutation Groups",
--   Springer GTM 163 (1996), DOI 10.1007/978-1-4612-0731-3.
--   Jean-Pierre Serre, "Linear Representations of Finite Groups",
--   Springer (1977), DOI 10.1007/978-1-4684-9458-7.
--
-- The map/table below is repository-specific finite computation; no Monster or
-- representation-theoretic identification is imported from these sources.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Sum using (inj₂)

import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

------------------------------------------------------------------------
-- Canonical normalized code for each nonunit phase class.
------------------------------------------------------------------------

phaseNonUnitRepresentative : Phase.NonUnitPhase7 → Tower.LevelTwoCode
phaseNonUnitRepresentative nonunit =
  Base.tri-low , Phase.forgetPhaseClass (inj₂ nonunit)

phaseSevenToShape : Phase.NonUnitPhase7 → Shape.ShapeOrbit7
phaseSevenToShape nonunit =
  Shape.shapeClass (phaseNonUnitRepresentative nonunit)

------------------------------------------------------------------------
-- Exact table.
------------------------------------------------------------------------

lowLowMapsConstant :
  phaseSevenToShape Phase.nonUnitLowLow ≡ Shape.constantShape
lowLowMapsConstant = refl

lowMidMapsRank2OneFixed :
  phaseSevenToShape Phase.nonUnitLowMid ≡ Shape.rank2OneFixedShape
lowMidMapsRank2OneFixed = refl

lowHighMapsRank2TwoFixed :
  phaseSevenToShape Phase.nonUnitLowHigh ≡ Shape.rank2TwoFixedShape
lowHighMapsRank2TwoFixed = refl

midLowMapsRank2TwoFixed :
  phaseSevenToShape Phase.nonUnitMidLow ≡ Shape.rank2TwoFixedShape
midLowMapsRank2TwoFixed = refl

midMidMapsRank2TwoFixed :
  phaseSevenToShape Phase.nonUnitMidMid ≡ Shape.rank2TwoFixedShape
midMidMapsRank2TwoFixed = refl

highLowMapsRank2OneFixed :
  phaseSevenToShape Phase.nonUnitHighLow ≡ Shape.rank2OneFixedShape
highLowMapsRank2OneFixed = refl

highHighMapsRank2TwoFixed :
  phaseSevenToShape Phase.nonUnitHighHigh ≡ Shape.rank2TwoFixedShape
highHighMapsRank2TwoFixed = refl

------------------------------------------------------------------------
-- Constructive non-injectivity.
------------------------------------------------------------------------

lowHighDistinctMidLow :
  Phase.nonUnitLowHigh ≡ Phase.nonUnitMidLow → ⊥
lowHighDistinctMidLow ()

lowHighAndMidLowCollide :
  phaseSevenToShape Phase.nonUnitLowHigh
  ≡ phaseSevenToShape Phase.nonUnitMidLow
lowHighAndMidLowCollide = refl

phaseSevenToShapeNotInjective :
  ((left right : Phase.NonUnitPhase7) →
    phaseSevenToShape left ≡ phaseSevenToShape right →
    left ≡ right) →
  ⊥
phaseSevenToShapeNotInjective injective =
  lowHighDistinctMidLow
    (injective
      Phase.nonUnitLowHigh
      Phase.nonUnitMidLow
      lowHighAndMidLowCollide)

------------------------------------------------------------------------
-- Exact image classification: only three of the seven conjugacy shapes occur.
------------------------------------------------------------------------

data PhaseSevenImage3 : Set where
  constantImage : PhaseSevenImage3
  rank2OneFixedImage : PhaseSevenImage3
  rank2TwoFixedImage : PhaseSevenImage3

imageTag : Phase.NonUnitPhase7 → PhaseSevenImage3
imageTag Phase.nonUnitLowLow = constantImage
imageTag Phase.nonUnitLowMid = rank2OneFixedImage
imageTag Phase.nonUnitLowHigh = rank2TwoFixedImage
imageTag Phase.nonUnitMidLow = rank2TwoFixedImage
imageTag Phase.nonUnitMidMid = rank2TwoFixedImage
imageTag Phase.nonUnitHighLow = rank2OneFixedImage
imageTag Phase.nonUnitHighHigh = rank2TwoFixedImage

shapeOfImageTag : PhaseSevenImage3 → Shape.ShapeOrbit7
shapeOfImageTag constantImage = Shape.constantShape
shapeOfImageTag rank2OneFixedImage = Shape.rank2OneFixedShape
shapeOfImageTag rank2TwoFixedImage = Shape.rank2TwoFixedShape

phaseSevenToShapeFactorsThroughImage3 :
  (nonunit : Phase.NonUnitPhase7) →
  phaseSevenToShape nonunit ≡ shapeOfImageTag (imageTag nonunit)
phaseSevenToShapeFactorsThroughImage3 Phase.nonUnitLowLow = refl
phaseSevenToShapeFactorsThroughImage3 Phase.nonUnitLowMid = refl
phaseSevenToShapeFactorsThroughImage3 Phase.nonUnitLowHigh = refl
phaseSevenToShapeFactorsThroughImage3 Phase.nonUnitMidLow = refl
phaseSevenToShapeFactorsThroughImage3 Phase.nonUnitMidMid = refl
phaseSevenToShapeFactorsThroughImage3 Phase.nonUnitHighLow = refl
phaseSevenToShapeFactorsThroughImage3 Phase.nonUnitHighHigh = refl

------------------------------------------------------------------------
-- Four shape classes are constructively excluded from the canonical image.
------------------------------------------------------------------------

identityNotInPhaseSevenImage :
  (nonunit : Phase.NonUnitPhase7) →
  phaseSevenToShape nonunit ≡ Shape.identityShape → ⊥
identityNotInPhaseSevenImage Phase.nonUnitLowLow ()
identityNotInPhaseSevenImage Phase.nonUnitLowMid ()
identityNotInPhaseSevenImage Phase.nonUnitLowHigh ()
identityNotInPhaseSevenImage Phase.nonUnitMidLow ()
identityNotInPhaseSevenImage Phase.nonUnitMidMid ()
identityNotInPhaseSevenImage Phase.nonUnitHighLow ()
identityNotInPhaseSevenImage Phase.nonUnitHighHigh ()

threeCycleNotInPhaseSevenImage :
  (nonunit : Phase.NonUnitPhase7) →
  phaseSevenToShape nonunit ≡ Shape.threeCycleShape → ⊥
threeCycleNotInPhaseSevenImage Phase.nonUnitLowLow ()
threeCycleNotInPhaseSevenImage Phase.nonUnitLowMid ()
threeCycleNotInPhaseSevenImage Phase.nonUnitLowHigh ()
threeCycleNotInPhaseSevenImage Phase.nonUnitMidLow ()
threeCycleNotInPhaseSevenImage Phase.nonUnitMidMid ()
threeCycleNotInPhaseSevenImage Phase.nonUnitHighLow ()
threeCycleNotInPhaseSevenImage Phase.nonUnitHighHigh ()

transpositionNotInPhaseSevenImage :
  (nonunit : Phase.NonUnitPhase7) →
  phaseSevenToShape nonunit ≡ Shape.transpositionShape → ⊥
transpositionNotInPhaseSevenImage Phase.nonUnitLowLow ()
transpositionNotInPhaseSevenImage Phase.nonUnitLowMid ()
transpositionNotInPhaseSevenImage Phase.nonUnitLowHigh ()
transpositionNotInPhaseSevenImage Phase.nonUnitMidLow ()
transpositionNotInPhaseSevenImage Phase.nonUnitMidMid ()
transpositionNotInPhaseSevenImage Phase.nonUnitHighLow ()
transpositionNotInPhaseSevenImage Phase.nonUnitHighHigh ()

rank2TwoCycleNotInPhaseSevenImage :
  (nonunit : Phase.NonUnitPhase7) →
  phaseSevenToShape nonunit ≡ Shape.rank2TwoCycleShape → ⊥
rank2TwoCycleNotInPhaseSevenImage Phase.nonUnitLowLow ()
rank2TwoCycleNotInPhaseSevenImage Phase.nonUnitLowMid ()
rank2TwoCycleNotInPhaseSevenImage Phase.nonUnitLowHigh ()
rank2TwoCycleNotInPhaseSevenImage Phase.nonUnitMidLow ()
rank2TwoCycleNotInPhaseSevenImage Phase.nonUnitMidMid ()
rank2TwoCycleNotInPhaseSevenImage Phase.nonUnitHighLow ()
rank2TwoCycleNotInPhaseSevenImage Phase.nonUnitHighHigh ()

------------------------------------------------------------------------
-- Boundary: this is a canonical comparison map, not an identification.
------------------------------------------------------------------------

record TernarySevenCanonicalMapBoundary : Set where
  constructor ternarySevenCanonicalMapBoundary
  field
    canonicalPhaseToShapeMapConstructed : Bool
    mapInjective : Bool
    mapSurjectiveOntoAllSevenShapes : Bool
    canonicalImageHasThreeShapeClasses : Bool
    equalSevenCardinalityCreatesNaturalBijection : Bool
    oggSevenIdentifiedByThisMap : Bool

canonicalTernarySevenCanonicalMapBoundary : TernarySevenCanonicalMapBoundary
canonicalTernarySevenCanonicalMapBoundary =
  ternarySevenCanonicalMapBoundary
    true false false true false false
