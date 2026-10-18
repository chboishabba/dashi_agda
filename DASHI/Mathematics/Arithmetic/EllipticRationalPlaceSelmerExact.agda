module DASHI.Mathematics.Arithmetic.EllipticRationalPlaceSelmerExact where

------------------------------------------------------------------------
-- BSD 2-DESCENT: ACTUAL PRIME-INDEXED FINITE PLACES OF Q
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _,_)
open import Data.Sum.Base using (_⊎_)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact as Descent

Divides : Nat → Nat → Set
Divides divisor value =
  Σ Nat (λ quotient → divisor * quotient ≡ value)

record PrimeNat (value : Nat) : Set where
  field
    atLeastTwo : suc (suc 0) ≤ value

    onlyTrivialDivisors :
      (divisor : Nat) →
      Divides divisor value →
      divisor ≡ suc 0 ⊎ divisor ≡ value

open PrimeNat public

record FinitePrime : Set where
  constructor finite-prime
  field
    primeValue : Nat
    primeProof : PrimeNat primeValue

open FinitePrime public

data RationalPlace : Set where
  infinitePlace : RationalPlace
  finitePlace : FinitePrime → RationalPlace

record RationalPlaceTwoDescentData
    (curve : Elliptic.ShortWeierstrassCurve) : Set₁ where
  field
    GlobalCohomology : Set
    InfiniteLocalCohomology : Set
    FiniteLocalCohomology : FinitePrime → Set

    localizeInfinity :
      GlobalCohomology → InfiniteLocalCohomology

    localizeFinite :
      (p : FinitePrime) →
      GlobalCohomology →
      FiniteLocalCohomology p

    GlobalKummerImage :
      GlobalCohomology → Set

    InfiniteKummerImage :
      InfiniteLocalCohomology → Set

    FiniteKummerImage :
      (p : FinitePrime) →
      FiniteLocalCohomology p →
      Set

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

    everyFinitePrimeCondition :
      (p : FinitePrime) →
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
  everyFinitePrimeCondition conditions p

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
    primePredicateOnFiniteLabelsPaid : Bool
    allPlaceConditionAssemblyPaid : Bool
    splitConditionsToSelmerCompilerPaid : Bool
    actualQvKummerRealizationPaid : Bool
    rationalSquareClassRealizationPaid : Bool
    globalSelmerComputationPaid : Bool
    shaTwoExactnessPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticRationalPlaceSelmerBoundary :
  EllipticRationalPlaceSelmerBoundary
canonicalEllipticRationalPlaceSelmerBoundary =
  elliptic-rational-place-selmer-boundary
    true true true true false false false false false
