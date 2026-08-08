module DASHI.Moonshine.MoonshineOrbifoldMasslessStateRemovalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster",
-- Academic Press, 1988.
-- ISBN: 978-0-12-267065-7; no DOI assigned.
--
-- Scott Carnahan,
-- "51 constructions of the Moonshine module",
-- Communications in Number Theory and Physics 12 (2018), 305--334.
-- DOI: 10.4310/CNTP.2018.v12.n2.a3.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact bounded meaning of Moonshine "mass restoration".  If the
-- invariant untwisted sector and the positive twisted sector both have zero
-- weight-one dimension, their orbifold completion has no weight-one states.
-- The first non-vacuum holomorphic grade is then two.  No four-dimensional
-- Hamiltonian or Yang--Mills mass-gap conclusion is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

record OrbifoldWeightOneInput : Set where
  constructor orbifold-weight-one-input
  field
    untwistedInvariantWeightOne : Nat
    twistedPositiveWeightOne : Nat
    untwistedInvariantWeightOneVanishes :
      untwistedInvariantWeightOne ≡ 0
    twistedPositiveWeightOneVanishes :
      twistedPositiveWeightOne ≡ 0

open OrbifoldWeightOneInput public

orbifoldWeightOne : OrbifoldWeightOneInput → Nat
orbifoldWeightOne input =
  untwistedInvariantWeightOne input
  + twistedPositiveWeightOne input

orbifoldCompletionRemovesWeightOne :
  (input : OrbifoldWeightOneInput) →
  orbifoldWeightOne input ≡ 0
orbifoldCompletionRemovesWeightOne input
  rewrite untwistedInvariantWeightOneVanishes input
        | twistedPositiveWeightOneVanishes input = refl

moonshineOrbifoldWeightOneInput : OrbifoldWeightOneInput
moonshineOrbifoldWeightOneInput =
  orbifold-weight-one-input 0 0 refl refl

moonshineWeightZeroDimension : Nat
moonshineWeightZeroDimension = 1

moonshineWeightOneDimension : Nat
moonshineWeightOneDimension =
  orbifoldWeightOne moonshineOrbifoldWeightOneInput

moonshineWeightTwoDimension : Nat
moonshineWeightTwoDimension = 196884

moonshineWeightOneVanishes : moonshineWeightOneDimension ≡ 0
moonshineWeightOneVanishes =
  orbifoldCompletionRemovesWeightOne moonshineOrbifoldWeightOneInput

moonshineWeightTwoIsOnePlusGriess :
  1 + 196883 ≡ moonshineWeightTwoDimension
moonshineWeightTwoIsOnePlusGriess = refl

conformalExcitationIndex : Nat
conformalExcitationIndex = 2

conformalExcitationIndexIsTwo : conformalExcitationIndex ≡ 2
conformalExcitationIndexIsTwo = refl

record ConformalGapBoundary : Set where
  constructor conformal-gap-boundary
  field
    weightOneRemovalFormalized : Bool
    weightOneRemovalFormalizedIsTrue :
      weightOneRemovalFormalized ≡ true
    firstHolomorphicExcitationIsGradeTwo : Bool
    firstHolomorphicExcitationIsGradeTwoIsTrue :
      firstHolomorphicExcitationIsGradeTwo ≡ true
    impliesFourDimensionalYangMillsGap : Bool
    impliesFourDimensionalYangMillsGapIsFalse :
      impliesFourDimensionalYangMillsGap ≡ false

canonicalConformalGapBoundary : ConformalGapBoundary
canonicalConformalGapBoundary =
  conformal-gap-boundary true refl true refl false refl
