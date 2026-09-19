module DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic

record GlobalLocalTwoDescentCarrier
    (curve : Elliptic.ShortWeierstrassCurve) : Set₁ where
  field
    GlobalCohomology : Set
    Place : Set
    LocalCohomology : Place → Set
    localize :
      (place : Place) → GlobalCohomology → LocalCohomology place
    GlobalKummerImage : GlobalCohomology → Set
    LocalKummerImage :
      (place : Place) → LocalCohomology place → Set

open GlobalLocalTwoDescentCarrier public

record SelmerTwoElement
    {curve : Elliptic.ShortWeierstrassCurve}
    (carrier : GlobalLocalTwoDescentCarrier curve) : Set₁ where
  field
    cohomologyClass : GlobalCohomology carrier
    satisfiesEveryLocalCondition :
      (place : Place carrier) →
      LocalKummerImage carrier place
        (localize carrier place cohomologyClass)

open SelmerTwoElement public

record MordellWeilShaTwoExactness
    {curve : Elliptic.ShortWeierstrassCurve}
    (carrier : GlobalLocalTwoDescentCarrier curve) : Set₁ where
  field
    MordellWeilModuloTwo : Set
    ShaTwo : Set
    kummerToSelmer :
      MordellWeilModuloTwo → SelmerTwoElement carrier
    selmerToSha :
      SelmerTwoElement carrier → ShaTwo
    kernelEqualsKummerImage : Set
    surjectiveOntoShaTwo : Set

open MordellWeilShaTwoExactness public

record EllipticTwoDescentRoadBoundary : Set where
  constructor elliptic-two-descent-road-boundary
  field
    globalLocalCarrierPaid : Bool
    selmerLocalConditionCarrierPaid : Bool
    rationalSquareClassInhabitantPaid : Bool
    localFieldKummerMapsPaid : Bool
    allPlaceConditionsPaid : Bool
    selmerGroupRealized : Bool
    mordellWeilModuloTwoRealized : Bool
    shaTwoRealized : Bool
    globalExactSequencePaid : Bool
    mordellWeilRankRealized : Bool
    shaFinitenessPaid : Bool

canonicalEllipticTwoDescentRoadBoundary :
  EllipticTwoDescentRoadBoundary
canonicalEllipticTwoDescentRoadBoundary =
  elliptic-two-descent-road-boundary
    true true false false false false false false false false false
