{-# OPTIONS --cubical --guardedness #-}

module DASHI.Physics.QFT.AQFTCubicalQuotientSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)
open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.HITs.SetQuotients.Base
  using (_/_; [_]; eq/; squash/)

------------------------------------------------------------------------
-- Optional cubical HIT quotient surface.
--
-- This module is deliberately standalone from the non-cubical AQFT surfaces.
-- It exposes Cubical Agda's set quotient HIT as an optional replacement
-- socket for the non-cubical setoid quotient authority surface.

data AQFTCubicalQuotientStatus : Set where
  cubicalHITQuotientOptionalNoPromotion :
    AQFTCubicalQuotientStatus

record AQFTCubicalHITQuotientSurface
  (Region : Set)
  (Carrier : Region → Set)
  (Relation :
    {region : Region} →
    Carrier region →
    Carrier region →
    Set) : Setω where
  field
    status :
      AQFTCubicalQuotientStatus

    CubicalQuotientCarrier :
      Region →
      Set

    cubicalQuotientCarrierIsHIT :
      (region : Region) →
      CubicalQuotientCarrier region
      ≡
      Carrier region / Relation {region}

    cubicalClass :
      {region : Region} →
      Carrier region →
      Carrier region / Relation {region}

    cubicalClassIsHITConstructor :
      {region : Region} →
      (x : Carrier region) →
      cubicalClass x
      ≡
      [ x ]

    cubicalRelationPath :
      {region : Region} →
      (x y : Carrier region) →
      Relation x y →
      cubicalClass x
      ≡
      cubicalClass y

    cubicalSetTruncation :
      {region : Region} →
      (x y : Carrier region / Relation {region}) →
      (p q : x ≡ y) →
      p ≡ q

    cubicalQuotientPromoted :
      Bool

    cubicalQuotientPromotedIsFalse :
      cubicalQuotientPromoted ≡ false

    cubicalQuotientBoundary :
      List String

open AQFTCubicalHITQuotientSurface public

canonicalAQFTCubicalHITQuotientSurface :
  (Region : Set) →
  (Carrier : Region → Set) →
  (Relation :
    {region : Region} →
    Carrier region →
    Carrier region →
    Set) →
  AQFTCubicalHITQuotientSurface Region Carrier Relation
canonicalAQFTCubicalHITQuotientSurface Region Carrier Relation =
  record
    { status =
        cubicalHITQuotientOptionalNoPromotion
    ; CubicalQuotientCarrier =
        λ region →
          Carrier region / Relation {region}
    ; cubicalQuotientCarrierIsHIT =
        λ _ → refl
    ; cubicalClass =
        λ x → [ x ]
    ; cubicalClassIsHITConstructor =
        λ _ → refl
    ; cubicalRelationPath =
        λ x y r → eq/ x y r
    ; cubicalSetTruncation =
        λ x y p q → squash/ x y p q
    ; cubicalQuotientPromoted =
        false
    ; cubicalQuotientPromotedIsFalse =
        refl
    ; cubicalQuotientBoundary =
        "Cubical HIT set quotient is available as an optional quotient carrier socket"
        ∷ "the main AQFT quotient surface remains non-cubical and does not depend on this module"
        ∷ "no C*-algebra, completion, GNS representation, time-slice theorem, or AQFT promotion is constructed here"
        ∷ []
    }
