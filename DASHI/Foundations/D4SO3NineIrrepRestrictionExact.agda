module DASHI.Foundations.D4SO3NineIrrepRestrictionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate the repository's existing five D4 irrep species with the
-- continuous SO(3) j=4 carrier.  The exact rotational-D4 restriction is
--
--   V_4 | D4 = 2 A1 + A2 + B1 + B2 + 2 E
--            = 1 + Reg_D4,
--
-- of total dimension nine.  Thus all five D4 irrep species occur in this
-- nine-dimensional restriction.
--
-- This is deliberately distinguished from the repository's existing D4
-- permutation action on a 3x3 nine-cell carrier, whose decomposition is
--
--   3 A1 + B1 + B2 + 2 E
--
-- and has no A2.  Equal dimension and equal symmetry group therefore do not
-- identify the two representation carriers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_)

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed

data D4RotationClass : Set where
  identityClass
    centralHalfTurnClass
    quarterTurnPairClass
    axisHalfTurnPairClass
    diagonalHalfTurnPairClass : D4RotationClass

d4Character : Candidate.D4IrrepKind → D4RotationClass → ℤ
d4Character Candidate.A1 identityClass = + 1
d4Character Candidate.A1 centralHalfTurnClass = + 1
d4Character Candidate.A1 quarterTurnPairClass = + 1
d4Character Candidate.A1 axisHalfTurnPairClass = + 1
d4Character Candidate.A1 diagonalHalfTurnPairClass = + 1

d4Character Candidate.A2 identityClass = + 1
d4Character Candidate.A2 centralHalfTurnClass = + 1
d4Character Candidate.A2 quarterTurnPairClass = + 1
d4Character Candidate.A2 axisHalfTurnPairClass = -[1+ 0 ]
d4Character Candidate.A2 diagonalHalfTurnPairClass = -[1+ 0 ]

d4Character Candidate.B1 identityClass = + 1
d4Character Candidate.B1 centralHalfTurnClass = + 1
d4Character Candidate.B1 quarterTurnPairClass = -[1+ 0 ]
d4Character Candidate.B1 axisHalfTurnPairClass = + 1
d4Character Candidate.B1 diagonalHalfTurnPairClass = -[1+ 0 ]

d4Character Candidate.B2 identityClass = + 1
d4Character Candidate.B2 centralHalfTurnClass = + 1
d4Character Candidate.B2 quarterTurnPairClass = -[1+ 0 ]
d4Character Candidate.B2 axisHalfTurnPairClass = -[1+ 0 ]
d4Character Candidate.B2 diagonalHalfTurnPairClass = + 1

d4Character Candidate.E2 identityClass = + 2
d4Character Candidate.E2 centralHalfTurnClass = -[1+ 1 ]
d4Character Candidate.E2 quarterTurnPairClass = + 0
d4Character Candidate.E2 axisHalfTurnPairClass = + 0
d4Character Candidate.E2 diagonalHalfTurnPairClass = + 0

j4D4Multiplicity : Candidate.D4IrrepKind → Nat
j4D4Multiplicity Candidate.A1 = 2
j4D4Multiplicity Candidate.A2 = 1
j4D4Multiplicity Candidate.B1 = 1
j4D4Multiplicity Candidate.B2 = 1
j4D4Multiplicity Candidate.E2 = 2

regularD4Multiplicity : Candidate.D4IrrepKind → Nat
regularD4Multiplicity Candidate.A1 = 1
regularD4Multiplicity Candidate.A2 = 1
regularD4Multiplicity Candidate.B1 = 1
regularD4Multiplicity Candidate.B2 = 1
regularD4Multiplicity Candidate.E2 = 2

trivialD4Multiplicity : Candidate.D4IrrepKind → Nat
trivialD4Multiplicity Candidate.A1 = 1
trivialD4Multiplicity Candidate.A2 = 0
trivialD4Multiplicity Candidate.B1 = 0
trivialD4Multiplicity Candidate.B2 = 0
trivialD4Multiplicity Candidate.E2 = 0

j4IsTrivialPlusRegular :
  (kind : Candidate.D4IrrepKind) →
  j4D4Multiplicity kind
  ≡ trivialD4Multiplicity kind + regularD4Multiplicity kind
j4IsTrivialPlusRegular Candidate.A1 = refl
j4IsTrivialPlusRegular Candidate.A2 = refl
j4IsTrivialPlusRegular Candidate.B1 = refl
j4IsTrivialPlusRegular Candidate.B2 = refl
j4IsTrivialPlusRegular Candidate.E2 = refl

j4D4Dimension : Nat
j4D4Dimension =
  j4D4Multiplicity Candidate.A1 * Candidate.irrepDimension Candidate.A1
  + j4D4Multiplicity Candidate.A2 * Candidate.irrepDimension Candidate.A2
  + j4D4Multiplicity Candidate.B1 * Candidate.irrepDimension Candidate.B1
  + j4D4Multiplicity Candidate.B2 * Candidate.irrepDimension Candidate.B2
  + j4D4Multiplicity Candidate.E2 * Candidate.irrepDimension Candidate.E2

j4D4DimensionIsNine : j4D4Dimension ≡ 9
j4D4DimensionIsNine = refl

j4D4DimensionMatchesSO3 : j4D4Dimension ≡ Spin.jDimension Spin.j4
j4D4DimensionMatchesSO3 = refl

scaleInt : Nat → ℤ → ℤ
scaleInt 0 value = + 0
scaleInt (suc n) value = value +ℤ scaleInt n value

j4D4BranchCharacter : D4RotationClass → ℤ
j4D4BranchCharacter class =
  scaleInt (j4D4Multiplicity Candidate.A1) (d4Character Candidate.A1 class)
  +ℤ scaleInt (j4D4Multiplicity Candidate.A2) (d4Character Candidate.A2 class)
  +ℤ scaleInt (j4D4Multiplicity Candidate.B1) (d4Character Candidate.B1 class)
  +ℤ scaleInt (j4D4Multiplicity Candidate.B2) (d4Character Candidate.B2 class)
  +ℤ scaleInt (j4D4Multiplicity Candidate.E2) (d4Character Candidate.E2 class)

j4SO3RestrictedCharacter : D4RotationClass → ℤ
j4SO3RestrictedCharacter identityClass = + 9
j4SO3RestrictedCharacter centralHalfTurnClass = Fixed.halfTurnCharacter 4
j4SO3RestrictedCharacter quarterTurnPairClass = + 1
j4SO3RestrictedCharacter axisHalfTurnPairClass = Fixed.halfTurnCharacter 4
j4SO3RestrictedCharacter diagonalHalfTurnPairClass = Fixed.halfTurnCharacter 4

j4D4CharacterExact :
  (class : D4RotationClass) →
  j4D4BranchCharacter class ≡ j4SO3RestrictedCharacter class
j4D4CharacterExact identityClass = refl
j4D4CharacterExact centralHalfTurnClass = refl
j4D4CharacterExact quarterTurnPairClass = refl
j4D4CharacterExact axisHalfTurnPairClass = refl
j4D4CharacterExact diagonalHalfTurnPairClass = refl

allFiveSpeciesPresentA1 : j4D4Multiplicity Candidate.A1 ≡ 2
allFiveSpeciesPresentA1 = refl
allFiveSpeciesPresentA2 : j4D4Multiplicity Candidate.A2 ≡ 1
allFiveSpeciesPresentA2 = refl
allFiveSpeciesPresentB1 : j4D4Multiplicity Candidate.B1 ≡ 1
allFiveSpeciesPresentB1 = refl
allFiveSpeciesPresentB2 : j4D4Multiplicity Candidate.B2 ≡ 1
allFiveSpeciesPresentB2 = refl
allFiveSpeciesPresentE : j4D4Multiplicity Candidate.E2 ≡ 2
allFiveSpeciesPresentE = refl

rawNineA2IsAbsent : Candidate.rawNineMultiplicity Candidate.A2 ≡ 0
rawNineA2IsAbsent = Candidate.rawA2MultiplicityIsZero

j4RestrictionA2IsPresent : j4D4Multiplicity Candidate.A2 ≡ 1
j4RestrictionA2IsPresent = refl

rawNinePermutationIsNotJ4Restriction :
  ((kind : Candidate.D4IrrepKind) →
    Candidate.rawNineMultiplicity kind ≡ j4D4Multiplicity kind) →
  ⊥
rawNinePermutationIsNotJ4Restriction same =
  zeroNotOne (trans rawNineA2IsAbsent (same Candidate.A2))
  where
    zeroNotOne : 0 ≡ 1 → ⊥
    zeroNotOne ()

record D4SO3NineRestrictionBoundary : Set where
  field
    fiveIrrepSpeciesOccurInSO3J4Restriction : Bool
    fiveIrrepSpeciesOccurInSO3J4RestrictionIsTrue :
      fiveIrrepSpeciesOccurInSO3J4Restriction ≡ true
    j4RestrictionIsTrivialPlusRegularD4 : Bool
    j4RestrictionIsTrivialPlusRegularD4IsTrue :
      j4RestrictionIsTrivialPlusRegularD4 ≡ true
    rawNineCellPermutationIdentifiedWithJ4Restriction : Bool
    rawNineCellPermutationIdentifiedWithJ4RestrictionIsFalse :
      rawNineCellPermutationIdentifiedWithJ4Restriction ≡ false
    equalDimensionImpliesEqualRepresentation : Bool
    equalDimensionImpliesEqualRepresentationIsFalse :
      equalDimensionImpliesEqualRepresentation ≡ false

canonicalD4SO3NineRestrictionBoundary : D4SO3NineRestrictionBoundary
canonicalD4SO3NineRestrictionBoundary =
  record
    { fiveIrrepSpeciesOccurInSO3J4Restriction = true
    ; fiveIrrepSpeciesOccurInSO3J4RestrictionIsTrue = refl
    ; j4RestrictionIsTrivialPlusRegularD4 = true
    ; j4RestrictionIsTrivialPlusRegularD4IsTrue = refl
    ; rawNineCellPermutationIdentifiedWithJ4Restriction = false
    ; rawNineCellPermutationIdentifiedWithJ4RestrictionIsFalse = refl
    ; equalDimensionImpliesEqualRepresentation = false
    ; equalDimensionImpliesEqualRepresentationIsFalse = refl
    }
