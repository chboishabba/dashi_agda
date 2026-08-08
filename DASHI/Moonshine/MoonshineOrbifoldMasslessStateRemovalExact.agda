module DASHI.Moonshine.MoonshineOrbifoldMasslessStateRemovalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster",
-- Pure and Applied Mathematics 134, Academic Press, 1988.
-- ISBN: 978-0-12-267065-7; no DOI assigned.
--
-- Scott Carnahan,
-- "51 constructions of the Moonshine module",
-- arXiv:1707.02954; no DOI assigned in this file.
--
-- Michael P. Tuite,
-- "On the relationship between monstrous Moonshine and the uniqueness of the
-- Moonshine module",
-- Communications in Mathematical Physics 166 (1995), 495--532.
-- arXiv:math/0506321; DOI not asserted here.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact finite logic behind the phrase "no massless states".
-- The untwisted invariant weight-one carrier and the retained twisted
-- weight-one carrier are each empty.  Their orbifold direct sum is therefore
-- empty.  Weight two is inhabited, so the first positive grade of the finite
-- profile is exactly two.
--
-- This does not identify a two-dimensional conformal grading gap with a
-- four-dimensional Yang--Mills Hamiltonian mass gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as W2

IsEmpty : Set → Set
IsEmpty A = A → ⊥

directSumOfEmptyIsEmpty :
  ∀ {A B : Set} → IsEmpty A → IsEmpty B → IsEmpty (A ⊎ B)
directSumOfEmptyIsEmpty emptyA emptyB (inj₁ a) = emptyA a
directSumOfEmptyIsEmpty emptyA emptyB (inj₂ b) = emptyB b

LeechWeightOneCurrent : Set
LeechWeightOneCurrent = Fin 24

UntwistedInvariantWeightOne : Set
UntwistedInvariantWeightOne = Fin 0

TwistedRetainedWeightOne : Set
TwistedRetainedWeightOne = Fin 0

MoonshineWeightOne : Set
MoonshineWeightOne =
  UntwistedInvariantWeightOne ⊎ TwistedRetainedWeightOne

untwistedInvariantWeightOneEmpty : IsEmpty UntwistedInvariantWeightOne
untwistedInvariantWeightOneEmpty ()

twistedRetainedWeightOneEmpty : IsEmpty TwistedRetainedWeightOne
twistedRetainedWeightOneEmpty ()

moonshineWeightOneEmpty : IsEmpty MoonshineWeightOne
moonshineWeightOneEmpty =
  directSumOfEmptyIsEmpty
    untwistedInvariantWeightOneEmpty
    twistedRetainedWeightOneEmpty

MoonshineWeightZero : Set
MoonshineWeightZero = Fin 1

MoonshineWeightTwo : Set
MoonshineWeightTwo = Fin W2.moonshineWeightTwoDimension

vacuumWitness : MoonshineWeightZero
vacuumWitness = zero

weightTwoExcitationWitness : MoonshineWeightTwo
weightTwoExcitationWitness = zero

record OrbifoldMasslessRemoval
    (FixedWeightOne TwistedWeightOne : Set) : Set where
  constructor orbifold-massless-removal
  field
    fixedWeightOneEmpty : IsEmpty FixedWeightOne
    twistedWeightOneEmpty : IsEmpty TwistedWeightOne

  OrbifoldWeightOne : Set
  OrbifoldWeightOne = FixedWeightOne ⊎ TwistedWeightOne

  orbifoldWeightOneEmpty : IsEmpty OrbifoldWeightOne
  orbifoldWeightOneEmpty =
    directSumOfEmptyIsEmpty fixedWeightOneEmpty twistedWeightOneEmpty

open OrbifoldMasslessRemoval public

canonicalOrbifoldMasslessRemoval :
  OrbifoldMasslessRemoval
    UntwistedInvariantWeightOne
    TwistedRetainedWeightOne
canonicalOrbifoldMasslessRemoval =
  orbifold-massless-removal
    untwistedInvariantWeightOneEmpty
    twistedRetainedWeightOneEmpty

record FiniteConformalExcitationProfile : Set where
  constructor finite-conformal-excitation-profile
  field
    vacuumGrade : Nat
    firstPositiveExcitationGrade : Nat
    vacuumGradeExact : vacuumGrade ≡ 0
    firstPositiveExcitationGradeExact :
      firstPositiveExcitationGrade ≡ 2
    noWeightOneState : IsEmpty MoonshineWeightOne
    weightTwoState : MoonshineWeightTwo

open FiniteConformalExcitationProfile public

canonicalFiniteConformalExcitationProfile :
  FiniteConformalExcitationProfile
canonicalFiniteConformalExcitationProfile =
  finite-conformal-excitation-profile
    0 2 refl refl moonshineWeightOneEmpty weightTwoExcitationWitness

conformalExcitationIndexIsTwo :
  firstPositiveExcitationGrade canonicalFiniteConformalExcitationProfile ≡ 2
conformalExcitationIndexIsTwo = refl

record MoonshineYangMillsGapBoundary : Set where
  constructor moonshine-yang-mills-gap-boundary
  field
    moonshineWeightOneRemovalConstructed :
      IsEmpty MoonshineWeightOne
    moonshineWeightTwoInhabited : MoonshineWeightTwo
    conformalExcitationIndex : Nat
    conformalExcitationIndexExact : conformalExcitationIndex ≡ 2
    conformalIndexProvesFourDimensionalYangMillsGap : Bool
    conformalIndexProvesFourDimensionalYangMillsGapIsFalse :
      conformalIndexProvesFourDimensionalYangMillsGap ≡ false
    dimensionfulScaleBridgeConstructed : Bool
    dimensionfulScaleBridgeConstructedIsFalse :
      dimensionfulScaleBridgeConstructed ≡ false

canonicalMoonshineYangMillsGapBoundary : MoonshineYangMillsGapBoundary
canonicalMoonshineYangMillsGapBoundary =
  moonshine-yang-mills-gap-boundary
    moonshineWeightOneEmpty
    weightTwoExcitationWitness
    2 refl
    false refl
    false refl
