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
-- Communications in Number Theory and Physics 12 (2018), 305--334.
-- DOI: 10.4310/CNTP.2018.v12.n2.a3; arXiv:1707.02954.
--
-- Michael P. Tuite,
-- "On the relationship between monstrous Moonshine and the uniqueness of the
-- Moonshine module",
-- Communications in Mathematical Physics 166 (1995), 495--532.
-- DOI: 10.1007/BF02099885; arXiv:hep-th/9305057.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact finite logic behind the phrase "no massless states".
-- The untwisted invariant weight-one carrier and the retained twisted
-- weight-one carrier are each empty.  Their orbifold direct sum is therefore
-- empty.  The typed FLM weight-two carrier is inhabited by a nonconformal
-- untwisted coordinate.  A grade-indexed 0/1/2 prefix proves that every
-- strictly positive represented grade below two is empty, so two is genuinely
-- the first positive grade of this prefix rather than a stored numeral.
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
MoonshineWeightTwo = W2.MoonshineWeightTwoCoordinate

vacuumWitness : MoonshineWeightZero
vacuumWitness = zero

weightTwoExcitationWitness : MoonshineWeightTwo
weightTwoExcitationWitness =
  W2.includeMonsterNontrivialCoordinate (inj₁ zero)

weightTwoExcitationIsNotConformalVector :
  weightTwoExcitationWitness ≡ W2.conformalVectorCoordinate → ⊥
weightTwoExcitationIsNotConformalVector ()

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

------------------------------------------------------------------------
-- Grade-indexed initial profile and genuine lower-grade minimality.
------------------------------------------------------------------------

data InitialConformalGrade : Set where
  gradeZero : InitialConformalGrade
  gradeOne : InitialConformalGrade
  gradeTwo : InitialConformalGrade

initialGradeValue : InitialConformalGrade → Nat
initialGradeValue gradeZero = 0
initialGradeValue gradeOne = 1
initialGradeValue gradeTwo = 2

InitialGradeCarrier : InitialConformalGrade → Set
InitialGradeCarrier gradeZero = MoonshineWeightZero
InitialGradeCarrier gradeOne = MoonshineWeightOne
InitialGradeCarrier gradeTwo = MoonshineWeightTwo

data PositiveGradeStrictlyBelowTwo : InitialConformalGrade → Set where
  gradeOneIsPositiveBelowTwo : PositiveGradeStrictlyBelowTwo gradeOne

allPositiveGradesBelowTwoAreEmpty :
  (grade : InitialConformalGrade) →
  PositiveGradeStrictlyBelowTwo grade →
  IsEmpty (InitialGradeCarrier grade)
allPositiveGradesBelowTwoAreEmpty gradeOne gradeOneIsPositiveBelowTwo =
  moonshineWeightOneEmpty

record FiniteConformalExcitationProfile : Set where
  constructor finite-conformal-excitation-profile
  field
    vacuumGrade : Nat
    firstPositiveExcitationGrade : Nat
    firstPositiveGradeTag : InitialConformalGrade
    vacuumGradeExact : vacuumGrade ≡ 0
    firstPositiveExcitationGradeExact :
      firstPositiveExcitationGrade ≡ 2
    firstPositiveGradeTagExact : firstPositiveGradeTag ≡ gradeTwo
    noWeightOneState : IsEmpty MoonshineWeightOne
    stateAtFirstPositiveGrade : InitialGradeCarrier firstPositiveGradeTag
    everyLowerPositiveGradeEmpty :
      (grade : InitialConformalGrade) →
      PositiveGradeStrictlyBelowTwo grade →
      IsEmpty (InitialGradeCarrier grade)
    weightTwoStateNonconformal :
      stateAtFirstPositiveGrade ≡ W2.conformalVectorCoordinate → ⊥

open FiniteConformalExcitationProfile public

canonicalFiniteConformalExcitationProfile :
  FiniteConformalExcitationProfile
canonicalFiniteConformalExcitationProfile =
  finite-conformal-excitation-profile
    0 2 gradeTwo
    refl refl refl
    moonshineWeightOneEmpty
    weightTwoExcitationWitness
    allPositiveGradesBelowTwoAreEmpty
    weightTwoExcitationIsNotConformalVector

conformalExcitationIndexIsTwo :
  firstPositiveExcitationGrade canonicalFiniteConformalExcitationProfile ≡ 2
conformalExcitationIndexIsTwo = refl

conformalExcitationMinimality :
  (grade : InitialConformalGrade) →
  PositiveGradeStrictlyBelowTwo grade →
  IsEmpty (InitialGradeCarrier grade)
conformalExcitationMinimality =
  everyLowerPositiveGradeEmpty canonicalFiniteConformalExcitationProfile

record MoonshineYangMillsGapBoundary : Set where
  constructor moonshine-yang-mills-gap-boundary
  field
    moonshineWeightOneRemovalConstructed :
      IsEmpty MoonshineWeightOne
    moonshineWeightTwoInhabited : MoonshineWeightTwo
    moonshineWeightTwoWitnessIsNonconformal :
      moonshineWeightTwoInhabited ≡ W2.conformalVectorCoordinate → ⊥
    everyStrictlyLowerPositiveInitialGradeEmpty :
      (grade : InitialConformalGrade) →
      PositiveGradeStrictlyBelowTwo grade →
      IsEmpty (InitialGradeCarrier grade)
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
    weightTwoExcitationIsNotConformalVector
    allPositiveGradesBelowTwoAreEmpty
    2 refl
    false refl
    false refl
