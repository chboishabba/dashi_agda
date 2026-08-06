module DASHI.Biology.MonsterWholeCarrierActionSchemaExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Springer, 1991.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Robert L. Griess,
-- "The Friendly Giant", Inventiones Mathematicae 69 (1982), 1--102.
-- DOI: 10.1007/BF01389186.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras",
-- Inventiones Mathematicae 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- DASHI CONTRIBUTION
--
-- Distinguish a coordinate decomposition from an invariant direct-sum
-- decomposition.  A total action may mix bulk and reduced coordinates while
-- preserving only a filtration, quotient, differential, or completed object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record TwoSectorState : Set where
  constructor twoSectorState
  field
    bulkCoordinate : Bool
    reducedCoordinate : Bool

open TwoSectorState public

mixCoordinates : TwoSectorState → TwoSectorState
mixCoordinates (twoSectorState bulk reduced) =
  twoSectorState reduced bulk

mixTwiceIsIdentity :
  (state : TwoSectorState) → mixCoordinates (mixCoordinates state) ≡ state
mixTwiceIsIdentity (twoSectorState false false) = refl
mixTwiceIsIdentity (twoSectorState false true) = refl
mixTwiceIsIdentity (twoSectorState true false) = refl
mixTwiceIsIdentity (twoSectorState true true) = refl

bulkOnly : TwoSectorState
bulkOnly = twoSectorState true false

reducedOnly : TwoSectorState
reducedOnly = twoSectorState false true

bulkCoordinateNotInvariantUnderMixing :
  mixCoordinates bulkOnly ≡ reducedOnly
bulkCoordinateNotInvariantUnderMixing = refl

reducedCoordinateNotInvariantUnderMixing :
  mixCoordinates reducedOnly ≡ bulkOnly
reducedCoordinateNotInvariantUnderMixing = refl

------------------------------------------------------------------------
-- Filtration-preserving and graded-preserving are separate declarations.
------------------------------------------------------------------------

data ActionCompatibility : Set where
  preservesDisplayedSummands : ActionCompatibility
  preservesFiltrationOnly : ActionCompatibility
  preservesAssociatedGradedOnly : ActionCompatibility
  intertwinesCompatibilityDifferential : ActionCompatibility
  mixesAllDisplayedCoordinates : ActionCompatibility

record WholeCarrierActionCandidate : Set where
  constructor wholeCarrierActionCandidate
  field
    compatibility : ActionCompatibility
    concreteMonsterElementAction : Bool
    concreteMonsterElementActionIsFalse :
      concreteMonsterElementAction ≡ false

open WholeCarrierActionCandidate public

filtrationCandidate : WholeCarrierActionCandidate
filtrationCandidate =
  wholeCarrierActionCandidate preservesFiltrationOnly false refl

gradingCandidate : WholeCarrierActionCandidate
gradingCandidate =
  wholeCarrierActionCandidate preservesAssociatedGradedOnly false refl

complexCandidate : WholeCarrierActionCandidate
complexCandidate =
  wholeCarrierActionCandidate intertwinesCompatibilityDifferential false refl

fullyMixedCandidate : WholeCarrierActionCandidate
fullyMixedCandidate =
  wholeCarrierActionCandidate mixesAllDisplayedCoordinates false refl

record WholeCarrierBoundary : Set where
  constructor wholeCarrierBoundary
  field
    coordinateSplitImpliesInvariantSplit : Bool
    coordinateSplitImpliesInvariantSplitIsFalse :
      coordinateSplitImpliesInvariantSplit ≡ false

    nonInvariantReducedCoordinatesAreAllowed : Bool
    nonInvariantReducedCoordinatesAreAllowedIsTrue :
      nonInvariantReducedCoordinatesAreAllowed ≡ true

    schemaConstructsMonsterAction : Bool
    schemaConstructsMonsterActionIsFalse :
      schemaConstructsMonsterAction ≡ false

canonicalWholeCarrierBoundary : WholeCarrierBoundary
canonicalWholeCarrierBoundary =
  wholeCarrierBoundary false refl true refl false refl
