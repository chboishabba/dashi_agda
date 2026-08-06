module DASHI.Biology.MonsterRepresentationRoutesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Springer, 1991.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- ISBN: 978-1-4684-9458-7. No DOI asserted here.
--
-- Robert L. Griess,
-- "The Friendly Giant", Inventiones Mathematicae 69 (1982), 1--102.
-- DOI: 10.1007/BF01389186.
--
-- DASHI CONTRIBUTION
--
-- Enumerate the logically distinct representation-theoretic routes by which
-- a 53-dimensional reduced carrier may participate in a larger
-- Monster-relevant construction without itself being a nontrivial
-- 53-dimensional Monster irreducible representation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Route tags keep hypotheses separate rather than collapsing them into one
-- vague "Monster connection" claim.
------------------------------------------------------------------------

data RepresentationRoute : Set where
  subgroupRestriction : RepresentationRoute
  inductionFromSubgroup : RepresentationRoute
  filteredExtension : RepresentationRoute
  associatedGraded : RepresentationRoute
  multiplicitySpace : RepresentationRoute
  nonInvariantCoordinates : RepresentationRoute
  compatibilityComplex : RepresentationRoute
  completionOrQuotient : RepresentationRoute
  fullSectorMixing : RepresentationRoute

data RouteStatus : Set where
  finiteCarrierConstructed : RouteStatus
  schemaOnly : RouteStatus
  externalWitnessRequired : RouteStatus
  ruledOutInDeclaredForm : RouteStatus

record RouteAssessment : Set where
  constructor routeAssessment
  field
    route : RepresentationRoute
    status : RouteStatus
    preservesFiftyThreeAsStandaloneMonsterIrrep : Bool
    preservesFiftyThreeAsStandaloneMonsterIrrepIsFalse :
      preservesFiftyThreeAsStandaloneMonsterIrrep ≡ false

open RouteAssessment public

restrictionAssessment : RouteAssessment
restrictionAssessment =
  routeAssessment subgroupRestriction externalWitnessRequired false refl

inductionAssessment : RouteAssessment
inductionAssessment =
  routeAssessment inductionFromSubgroup externalWitnessRequired false refl

filtrationAssessment : RouteAssessment
filtrationAssessment =
  routeAssessment filteredExtension finiteCarrierConstructed false refl

gradingAssessment : RouteAssessment
gradingAssessment =
  routeAssessment associatedGraded finiteCarrierConstructed false refl

multiplicityAssessment : RouteAssessment
multiplicityAssessment =
  routeAssessment multiplicitySpace schemaOnly false refl

coordinateAssessment : RouteAssessment
coordinateAssessment =
  routeAssessment nonInvariantCoordinates finiteCarrierConstructed false refl

complexAssessment : RouteAssessment
complexAssessment =
  routeAssessment compatibilityComplex schemaOnly false refl

completionAssessment : RouteAssessment
completionAssessment =
  routeAssessment completionOrQuotient schemaOnly false refl

mixingAssessment : RouteAssessment
mixingAssessment =
  routeAssessment fullSectorMixing schemaOnly false refl

------------------------------------------------------------------------
-- A finite mixing witness: the displayed coordinates need not be invariant.
------------------------------------------------------------------------

data Sector : Set where
  bulkSector : Sector
  reducedSector : Sector

data MixedCoordinate : Set where
  bulkBasis : MixedCoordinate
  reducedBasis : MixedCoordinate

swapSectors : MixedCoordinate → MixedCoordinate
swapSectors bulkBasis = reducedBasis
swapSectors reducedBasis = bulkBasis

bulkNotPreservedBySwap : swapSectors bulkBasis ≡ reducedBasis
bulkNotPreservedBySwap = refl

reducedNotPreservedBySwap : swapSectors reducedBasis ≡ bulkBasis
reducedNotPreservedBySwap = refl

record RouteBoundary : Set where
  constructor routeBoundary
  field
    reducedCarrierStandaloneNontrivialMonsterIrrepClaimed : Bool
    reducedCarrierStandaloneNontrivialMonsterIrrepClaimedIsFalse :
      reducedCarrierStandaloneNontrivialMonsterIrrepClaimed ≡ false

    wholeCarrierMayMixDisplayedCoordinates : Bool
    wholeCarrierMayMixDisplayedCoordinatesIsTrue :
      wholeCarrierMayMixDisplayedCoordinates ≡ true

    anyConcreteMonsterRouteCompleted : Bool
    anyConcreteMonsterRouteCompletedIsFalse :
      anyConcreteMonsterRouteCompleted ≡ false

canonicalRouteBoundary : RouteBoundary
canonicalRouteBoundary = routeBoundary false refl true refl false refl
