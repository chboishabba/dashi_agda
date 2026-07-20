module DASHI.Philosophy.LocalChartLaws where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Executable global chart calculus.  Partial-domain refinements live in the
-- atlas layer; this package proves the ordinary inverse and cocycle laws.

record InvertibleChart (X Coordinate : Set) : Set₁ where
  field
    normalise : X → Coordinate
    denormalise : Coordinate → X
    denormaliseAfterNormalise : (x : X) → denormalise (normalise x) ≡ x
    normaliseAfterDenormalise : (c : Coordinate) → normalise (denormalise c) ≡ c

open InvertibleChart public

transition :
  ∀ {X Coordinate : Set} →
  InvertibleChart X Coordinate →
  InvertibleChart X Coordinate →
  Coordinate → Coordinate
transition source target c =
  normalise target (denormalise source c)

transitionIdentity :
  ∀ {X Coordinate : Set}
    (chart : InvertibleChart X Coordinate)
    (c : Coordinate) →
  transition chart chart c ≡ c
transitionIdentity chart c =
  normaliseAfterDenormalise chart c

transitionCocycle :
  ∀ {X Coordinate : Set}
    (first second third : InvertibleChart X Coordinate)
    (c : Coordinate) →
  transition second third (transition first second c)
  ≡ transition first third c
transitionCocycle first second third c
  rewrite denormaliseAfterNormalise second (denormalise first c) = refl

normaliseRoundTrip :
  ∀ {X Coordinate : Set}
    (chart : InvertibleChart X Coordinate)
    (x : X) →
  denormalise chart (normalise chart x) ≡ x
normaliseRoundTrip chart = denormaliseAfterNormalise chart

denormaliseUnitReturnsStar :
  ∀ {X Coordinate : Set}
    (chart : InvertibleChart X Coordinate)
    (star : X)
    (unit : Coordinate) →
  normalise chart star ≡ unit →
  denormalise chart unit ≡ star
denormaliseUnitReturnsStar chart star unit starNormalisesToUnit
  rewrite starNormalisesToUnit = denormaliseAfterNormalise chart star
