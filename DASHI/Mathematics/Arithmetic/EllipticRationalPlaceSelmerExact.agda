module DASHI.Mathematics.Arithmetic.EllipticRationalPlaceSelmerExact where

------------------------------------------------------------------------
-- BSD 2-DESCENT: MAKE "ALL PLACES OF Q" AN EXPLICIT SPLIT
--
-- This owner does not construct Q_v.  It pays the indexing/assembly theorem:
-- one infinite place plus a family of finite-place local conditions compile
-- into the single all-place predicate consumed by SelmerTwoElement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact as Descent

data RationalPlace : Set where
  infinitePlace : RationalPlace
  finitePlace : Nat → RationalPlace

record RationalPlaceTwoDescentData
    (curve : Elliptic.ShortWeierstrassCurve) : Set₁ where
  field
    GlobalCohomology : Set
    InfiniteLocalCohomology : Set
    FiniteLocalCohomology : Nat → Set

    localizeInfinity :
      GlobalCohomology → InfiniteLocalCohomology

    localizeFinite :
      (p : Nat) → GlobalCohomology → FiniteLocalCohomology p

    GlobalKummerImage :
      GlobalCohomology → Set

    InfiniteKummerImage :
      InfiniteLocalCohomology → Set

    FiniteKummerImage :
      (p : Nat) → FiniteLocalCohomology p → Set

open RationalPlaceTwoDescentData public

rationalPlaceCarrier :
  ∀ {curve} →
  RationalPlaceTwoDescentData curve →
  Descent.GlobalLocalTwoDescentCarrier curve
rationalPlaceCarrier data = record
  { Descent.GlobalCohomology = GlobalCohomology data
  ; Descent.Place = RationalPlace
  ; Descent.LocalCohomology = λ where
      infinitePlace → InfiniteLocalCohomology data
      (finitePlace p) → FiniteLocalCohomology data p
  ; Descent.localize = λ where
      infinitePlace → localizeInfinity data
      (finitePlace p) → localizeFinite data p
  ; Descent.GlobalKummerImage = GlobalKummerImage data
  ; Descent.LocalKummerImage = λ where
      infinitePlace → InfiniteKummerImage data
      (finitePlace p) → FiniteKummerImage data p
  }

record RationalSelmerConditions
    {curve : Elliptic.ShortWeierstrassCurve}
    (data : RationalPlaceTwoDescentData curve)
    (cohomologyClass : GlobalCohomology data) : Set₁ where
  field
    infiniteCondition :
      InfiniteKummerImage data
        (localizeInfinity data cohomologyClass)

    everyFiniteCondition :
      (p : Nat) →
      FiniteKummerImage data p
        (localizeFinite data p cohomologyClass)

open RationalSelmerConditions public

rationalConditionsGiveAllPlaces :
  ∀ {curve data cohomologyClass} →
  RationalSelmerConditions
    {curve = curve} data cohomologyClass →
  (place : Descent.Place (rationalPlaceCarrier data)) →
  Descent.LocalKummerImage
    (rationalPlaceCarrier data)
    place
    (Descent.localize
      (rationalPlaceCarrier data)
      place
      cohomologyClass)
rationalConditionsGiveAllPlaces conditions infinitePlace =
  infiniteCondition conditions
rationalConditionsGiveAllPlaces conditions (finitePlace p) =
  everyFiniteCondition conditions p

rationalConditionsGiveSelmerElement :
  ∀ {curve data}
    (cohomologyClass : GlobalCohomology data) →
  RationalSelmerConditions
    {curve = curve} data cohomologyClass →
  Descent.SelmerTwoElement (rationalPlaceCarrier data)
rationalConditionsGiveSelmerElement cohomologyClass conditions = record
  { Descent.cohomologyClass = cohomologyClass
  ; Descent.satisfiesEveryLocalCondition =
      rationalConditionsGiveAllPlaces conditions
  }

record EllipticRationalPlaceSelmerBoundary : Set where
  constructor elliptic-rational-place-selmer-boundary
  field
    rationalPlaceSplitPaid : Bool
    allPlaceConditionAssemblyPaid : Bool
    splitConditionsToSelmerCompilerPaid : Bool
    primePredicateOnFiniteLabelsPaid : Bool
    actualQvKummerRealizationPaid : Bool
    rationalSquareClassRealizationPaid : Bool
    globalSelmerComputationPaid : Bool
    shaTwoExactnessPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticRationalPlaceSelmerBoundary :
  EllipticRationalPlaceSelmerBoundary
canonicalEllipticRationalPlaceSelmerBoundary =
  elliptic-rational-place-selmer-boundary
    true true true false false false false false false
