module DASHI.Reasoning.Trialectic369OrbifoldCoordinateRetractionWrongTypeExact where

------------------------------------------------------------------------
-- ORBIFOLD WEIGHT-TWO COORDINATE RETRACTION: USEFUL, BUT WRONG TYPE
--
-- SOURCE OWNER
--
-- MoonshineOrbifoldWeightTwoDecompositionExact gives typed coordinate carriers:
--
--   MoonshineWeightTwoCoordinate
--     = conformal line + nonconformal untwisted + twisted;
--
--   MonsterNontrivialWeightTwoCoordinate
--     = nonconformal untwisted + twisted.
--
-- Its inclusion of the 196883-coordinate carrier therefore has an exact
-- partial projection / left inverse.  This proves coordinate-level
-- faithfulness of THAT inclusion.
--
-- DASHI CONTRIBUTION
--
-- Make the retraction explicit and keep the type firewall:
-- this coordinate retraction is not a linear projection on the HilbertLift
-- constituent inclusion used by the canonical selected-3B linear core.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as Orbifold
import DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact as LinearRetraction

------------------------------------------------------------------------
-- 1. Exact partial projection.
------------------------------------------------------------------------

projectMonsterNontrivialCoordinate :
  Orbifold.MoonshineWeightTwoCoordinate →
  Maybe Orbifold.MonsterNontrivialWeightTwoCoordinate
projectMonsterNontrivialCoordinate (inj₁ (inj₁ conformal)) = nothing
projectMonsterNontrivialCoordinate (inj₁ (inj₂ untwisted)) =
  just (inj₁ untwisted)
projectMonsterNontrivialCoordinate (inj₂ twisted) =
  just (inj₂ twisted)

coordinateProjectionLeftInverse :
  (coordinate : Orbifold.MonsterNontrivialWeightTwoCoordinate) →
  projectMonsterNontrivialCoordinate
    (Orbifold.includeMonsterNontrivialCoordinate coordinate)
  ≡ just coordinate
coordinateProjectionLeftInverse (inj₁ untwisted) = refl
coordinateProjectionLeftInverse (inj₂ twisted) = refl

coordinateInclusionInjective :
  ∀ {left right : Orbifold.MonsterNontrivialWeightTwoCoordinate} →
  Orbifold.includeMonsterNontrivialCoordinate left
  ≡ Orbifold.includeMonsterNontrivialCoordinate right
  →
  left ≡ right
coordinateInclusionInjective {left} {right} equality
  with cong projectMonsterNontrivialCoordinate equality
... | projected
  rewrite coordinateProjectionLeftInverse left
        | coordinateProjectionLeftInverse right = justInjective projected
  where
    justInjective :
      ∀ {A : Set} {x y : A} →
      just x ≡ just y →
      x ≡ y
    justInjective refl = refl

conformalProjectsToNothing :
  projectMonsterNontrivialCoordinate
    Orbifold.conformalVectorCoordinate
  ≡ nothing
conformalProjectsToNothing = refl

------------------------------------------------------------------------
-- 2. Wrong-type separation from the canonical LINEAR retraction.
------------------------------------------------------------------------

data CoordinateRetractionCreatesLinearHilbertRetraction : Set where
data CoordinateInjectivityCreatesLinearInclusionInjectivity : Set where
data DimensionSplitCreatesSameObjectLinearProjection : Set where

coordinateRetractionDoesNotCreateLinearHilbertRetraction :
  CoordinateRetractionCreatesLinearHilbertRetraction → ⊥
coordinateRetractionDoesNotCreateLinearHilbertRetraction ()

coordinateInjectivityDoesNotCreateLinearInjectivity :
  CoordinateInjectivityCreatesLinearInclusionInjectivity → ⊥
coordinateInjectivityDoesNotCreateLinearInjectivity ()

dimensionSplitDoesNotCreateSameObjectLinearProjection :
  DimensionSplitCreatesSameObjectLinearProjection → ⊥
dimensionSplitDoesNotCreateSameObjectLinearProjection ()

------------------------------------------------------------------------
-- 3. Recognition boundary.
------------------------------------------------------------------------

record OrbifoldCoordinateRetractionBoundary : Set where
  constructor orbifold-coordinate-retraction-boundary
  field
    typed196883CoordinateInclusionOwned : Bool
    coordinatePartialProjectionOwned : Bool
    projectionLeftInverseOnMonsterCoordinates : Bool
    coordinateInclusionInjectivePaid : Bool
    conformalCoordinateMapsToNothing : Bool
    linearHilbertRetractionConstructed : Bool
    canonicalSelected3BFaithfulnessPaidByThisModule : Bool

canonicalOrbifoldCoordinateRetractionBoundary :
  OrbifoldCoordinateRetractionBoundary
canonicalOrbifoldCoordinateRetractionBoundary =
  orbifold-coordinate-retraction-boundary
    true true true true true
    false false
