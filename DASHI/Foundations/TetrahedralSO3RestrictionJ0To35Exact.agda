module DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Restrict the SO(3) angular-momentum scan j=0..35 to the rotational
-- tetrahedral group T ~= A4.  The four complex irrep species have dimensions
-- 1,1,1,3.  The two conjugate one-dimensional species are kept distinct in an
-- exact Eisenstein carrier a+b*omega with omega^2+omega+1=0.
--
-- The exact regular-shift law is
--
--   Res_A4 V_(j+6) = Res_A4 V_j + Reg_A4,
--
-- wherever both sides lie in the scan.  In particular dimension 3 (j=1) and
-- dimension 15 (j=7) differ by one regular representation, providing an
-- Ogg/non-Ogg control independent of the S4 and A5 collisions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_)

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed

data TetrahedralIrrep : Set where
  T1 T1Omega T1OmegaSquared T3 : TetrahedralIrrep

tetrahedralIrrepDimension : TetrahedralIrrep → Nat
tetrahedralIrrepDimension T1 = 1
tetrahedralIrrepDimension T1Omega = 1
tetrahedralIrrepDimension T1OmegaSquared = 1
tetrahedralIrrepDimension T3 = 3

data TetrahedralClass : Set where
  identityClass halfTurnClass thirdTurnClass thirdTurnInverseClass : TetrahedralClass

record EisensteinInt : Set where
  constructor eisenstein
  field
    onePart omegaPart : ℤ

open EisensteinInt public

zeroE oneE omegaE omegaSquaredE minusOneE : EisensteinInt
zeroE = eisenstein (+ 0) (+ 0)
oneE = eisenstein (+ 1) (+ 0)
omegaE = eisenstein (+ 0) (+ 1)
omegaSquaredE = eisenstein (-[1+ 0 ]) (-[1+ 0 ])
minusOneE = eisenstein (-[1+ 0 ]) (+ 0)

addE : EisensteinInt → EisensteinInt → EisensteinInt
addE left right =
  eisenstein
    (onePart left +ℤ onePart right)
    (omegaPart left +ℤ omegaPart right)

scaleE : Nat → EisensteinInt → EisensteinInt
scaleE 0 value = zeroE
scaleE (suc n) value = addE value (scaleE n value)

integerE : ℤ → EisensteinInt
integerE value = eisenstein value (+ 0)

irrepCharacter : TetrahedralIrrep → TetrahedralClass → EisensteinInt
irrepCharacter T1 identityClass = oneE
irrepCharacter T1 halfTurnClass = oneE
irrepCharacter T1 thirdTurnClass = oneE
irrepCharacter T1 thirdTurnInverseClass = oneE
irrepCharacter T1Omega identityClass = oneE
irrepCharacter T1Omega halfTurnClass = oneE
irrepCharacter T1Omega thirdTurnClass = omegaE
irrepCharacter T1Omega thirdTurnInverseClass = omegaSquaredE
irrepCharacter T1OmegaSquared identityClass = oneE
irrepCharacter T1OmegaSquared halfTurnClass = oneE
irrepCharacter T1OmegaSquared thirdTurnClass = omegaSquaredE
irrepCharacter T1OmegaSquared thirdTurnInverseClass = omegaE
irrepCharacter T3 identityClass = eisenstein (+ 3) (+ 0)
irrepCharacter T3 halfTurnClass = minusOneE
irrepCharacter T3 thirdTurnClass = zeroE
irrepCharacter T3 thirdTurnInverseClass = zeroE

record TetrahedralSpectrum : Set where
  constructor tet-spectrum
  field
    multiplicityT1 multiplicityT1Omega multiplicityT1OmegaSquared multiplicityT3 : Nat

open TetrahedralSpectrum public

branchingSpectrum : Spin.AngularMomentum0To35 → TetrahedralSpectrum
branchingSpectrum Spin.j0 = tet-spectrum 1 0 0 0
branchingSpectrum Spin.j1 = tet-spectrum 0 0 0 1
branchingSpectrum Spin.j2 = tet-spectrum 0 1 1 1
branchingSpectrum Spin.j3 = tet-spectrum 1 0 0 2
branchingSpectrum Spin.j4 = tet-spectrum 1 1 1 2
branchingSpectrum Spin.j5 = tet-spectrum 0 1 1 3
branchingSpectrum Spin.j6 = tet-spectrum 2 1 1 3
branchingSpectrum Spin.j7 = tet-spectrum 1 1 1 4
branchingSpectrum Spin.j8 = tet-spectrum 1 2 2 4
branchingSpectrum Spin.j9 = tet-spectrum 2 1 1 5
branchingSpectrum Spin.j10 = tet-spectrum 2 2 2 5
branchingSpectrum Spin.j11 = tet-spectrum 1 2 2 6
branchingSpectrum Spin.j12 = tet-spectrum 3 2 2 6
branchingSpectrum Spin.j13 = tet-spectrum 2 2 2 7
branchingSpectrum Spin.j14 = tet-spectrum 2 3 3 7
branchingSpectrum Spin.j15 = tet-spectrum 3 2 2 8
branchingSpectrum Spin.j16 = tet-spectrum 3 3 3 8
branchingSpectrum Spin.j17 = tet-spectrum 2 3 3 9
branchingSpectrum Spin.j18 = tet-spectrum 4 3 3 9
branchingSpectrum Spin.j19 = tet-spectrum 3 3 3 10
branchingSpectrum Spin.j20 = tet-spectrum 3 4 4 10
branchingSpectrum Spin.j21 = tet-spectrum 4 3 3 11
branchingSpectrum Spin.j22 = tet-spectrum 4 4 4 11
branchingSpectrum Spin.j23 = tet-spectrum 3 4 4 12
branchingSpectrum Spin.j24 = tet-spectrum 5 4 4 12
branchingSpectrum Spin.j25 = tet-spectrum 4 4 4 13
branchingSpectrum Spin.j26 = tet-spectrum 4 5 5 13
branchingSpectrum Spin.j27 = tet-spectrum 5 4 4 14
branchingSpectrum Spin.j28 = tet-spectrum 5 5 5 14
branchingSpectrum Spin.j29 = tet-spectrum 4 5 5 15
branchingSpectrum Spin.j30 = tet-spectrum 6 5 5 15
branchingSpectrum Spin.j31 = tet-spectrum 5 5 5 16
branchingSpectrum Spin.j32 = tet-spectrum 5 6 6 16
branchingSpectrum Spin.j33 = tet-spectrum 6 5 5 17
branchingSpectrum Spin.j34 = tet-spectrum 6 6 6 17
branchingSpectrum Spin.j35 = tet-spectrum 5 6 6 18

branchingDimension : TetrahedralSpectrum → Nat
branchingDimension spectrum =
  multiplicityT1 spectrum
  + multiplicityT1Omega spectrum
  + multiplicityT1OmegaSquared spectrum
  + 3 * multiplicityT3 spectrum

branchingDimensionExact :
  (j : Spin.AngularMomentum0To35) →
  branchingDimension (branchingSpectrum j) ≡ Spin.jDimension j
branchingDimensionExact Spin.j0 = refl
branchingDimensionExact Spin.j1 = refl
branchingDimensionExact Spin.j2 = refl
branchingDimensionExact Spin.j3 = refl
branchingDimensionExact Spin.j4 = refl
branchingDimensionExact Spin.j5 = refl
branchingDimensionExact Spin.j6 = refl
branchingDimensionExact Spin.j7 = refl
branchingDimensionExact Spin.j8 = refl
branchingDimensionExact Spin.j9 = refl
branchingDimensionExact Spin.j10 = refl
branchingDimensionExact Spin.j11 = refl
branchingDimensionExact Spin.j12 = refl
branchingDimensionExact Spin.j13 = refl
branchingDimensionExact Spin.j14 = refl
branchingDimensionExact Spin.j15 = refl
branchingDimensionExact Spin.j16 = refl
branchingDimensionExact Spin.j17 = refl
branchingDimensionExact Spin.j18 = refl
branchingDimensionExact Spin.j19 = refl
branchingDimensionExact Spin.j20 = refl
branchingDimensionExact Spin.j21 = refl
branchingDimensionExact Spin.j22 = refl
branchingDimensionExact Spin.j23 = refl
branchingDimensionExact Spin.j24 = refl
branchingDimensionExact Spin.j25 = refl
branchingDimensionExact Spin.j26 = refl
branchingDimensionExact Spin.j27 = refl
branchingDimensionExact Spin.j28 = refl
branchingDimensionExact Spin.j29 = refl
branchingDimensionExact Spin.j30 = refl
branchingDimensionExact Spin.j31 = refl
branchingDimensionExact Spin.j32 = refl
branchingDimensionExact Spin.j33 = refl
branchingDimensionExact Spin.j34 = refl
branchingDimensionExact Spin.j35 = refl

regularSpectrum : TetrahedralSpectrum
regularSpectrum = tet-spectrum 1 1 1 3

addSpectrum : TetrahedralSpectrum → TetrahedralSpectrum → TetrahedralSpectrum
addSpectrum left right =
  tet-spectrum
    (multiplicityT1 left + multiplicityT1 right)
    (multiplicityT1Omega left + multiplicityT1Omega right)
    (multiplicityT1OmegaSquared left + multiplicityT1OmegaSquared right)
    (multiplicityT3 left + multiplicityT3 right)

data LowJ0To29 : Set where
  lowJ0 lowJ1 lowJ2 lowJ3 lowJ4 lowJ5 lowJ6 lowJ7 lowJ8 lowJ9
    lowJ10 lowJ11 lowJ12 lowJ13 lowJ14 lowJ15 lowJ16 lowJ17 lowJ18 lowJ19
    lowJ20 lowJ21 lowJ22 lowJ23 lowJ24 lowJ25 lowJ26 lowJ27 lowJ28 lowJ29 : LowJ0To29

embedLowJ : LowJ0To29 → Spin.AngularMomentum0To35
embedLowJ lowJ0 = Spin.j0
embedLowJ lowJ1 = Spin.j1
embedLowJ lowJ2 = Spin.j2
embedLowJ lowJ3 = Spin.j3
embedLowJ lowJ4 = Spin.j4
embedLowJ lowJ5 = Spin.j5
embedLowJ lowJ6 = Spin.j6
embedLowJ lowJ7 = Spin.j7
embedLowJ lowJ8 = Spin.j8
embedLowJ lowJ9 = Spin.j9
embedLowJ lowJ10 = Spin.j10
embedLowJ lowJ11 = Spin.j11
embedLowJ lowJ12 = Spin.j12
embedLowJ lowJ13 = Spin.j13
embedLowJ lowJ14 = Spin.j14
embedLowJ lowJ15 = Spin.j15
embedLowJ lowJ16 = Spin.j16
embedLowJ lowJ17 = Spin.j17
embedLowJ lowJ18 = Spin.j18
embedLowJ lowJ19 = Spin.j19
embedLowJ lowJ20 = Spin.j20
embedLowJ lowJ21 = Spin.j21
embedLowJ lowJ22 = Spin.j22
embedLowJ lowJ23 = Spin.j23
embedLowJ lowJ24 = Spin.j24
embedLowJ lowJ25 = Spin.j25
embedLowJ lowJ26 = Spin.j26
embedLowJ lowJ27 = Spin.j27
embedLowJ lowJ28 = Spin.j28
embedLowJ lowJ29 = Spin.j29

shiftLowJBy6 : LowJ0To29 → Spin.AngularMomentum0To35
shiftLowJBy6 lowJ0 = Spin.j6
shiftLowJBy6 lowJ1 = Spin.j7
shiftLowJBy6 lowJ2 = Spin.j8
shiftLowJBy6 lowJ3 = Spin.j9
shiftLowJBy6 lowJ4 = Spin.j10
shiftLowJBy6 lowJ5 = Spin.j11
shiftLowJBy6 lowJ6 = Spin.j12
shiftLowJBy6 lowJ7 = Spin.j13
shiftLowJBy6 lowJ8 = Spin.j14
shiftLowJBy6 lowJ9 = Spin.j15
shiftLowJBy6 lowJ10 = Spin.j16
shiftLowJBy6 lowJ11 = Spin.j17
shiftLowJBy6 lowJ12 = Spin.j18
shiftLowJBy6 lowJ13 = Spin.j19
shiftLowJBy6 lowJ14 = Spin.j20
shiftLowJBy6 lowJ15 = Spin.j21
shiftLowJBy6 lowJ16 = Spin.j22
shiftLowJBy6 lowJ17 = Spin.j23
shiftLowJBy6 lowJ18 = Spin.j24
shiftLowJBy6 lowJ19 = Spin.j25
shiftLowJBy6 lowJ20 = Spin.j26
shiftLowJBy6 lowJ21 = Spin.j27
shiftLowJBy6 lowJ22 = Spin.j28
shiftLowJBy6 lowJ23 = Spin.j29
shiftLowJBy6 lowJ24 = Spin.j30
shiftLowJBy6 lowJ25 = Spin.j31
shiftLowJBy6 lowJ26 = Spin.j32
shiftLowJBy6 lowJ27 = Spin.j33
shiftLowJBy6 lowJ28 = Spin.j34
shiftLowJBy6 lowJ29 = Spin.j35

regularShiftBy6Exact :
  (j : LowJ0To29) →
  branchingSpectrum (shiftLowJBy6 j)
  ≡ addSpectrum regularSpectrum (branchingSpectrum (embedLowJ j))
regularShiftBy6Exact lowJ0 = refl
regularShiftBy6Exact lowJ1 = refl
regularShiftBy6Exact lowJ2 = refl
regularShiftBy6Exact lowJ3 = refl
regularShiftBy6Exact lowJ4 = refl
regularShiftBy6Exact lowJ5 = refl
regularShiftBy6Exact lowJ6 = refl
regularShiftBy6Exact lowJ7 = refl
regularShiftBy6Exact lowJ8 = refl
regularShiftBy6Exact lowJ9 = refl
regularShiftBy6Exact lowJ10 = refl
regularShiftBy6Exact lowJ11 = refl
regularShiftBy6Exact lowJ12 = refl
regularShiftBy6Exact lowJ13 = refl
regularShiftBy6Exact lowJ14 = refl
regularShiftBy6Exact lowJ15 = refl
regularShiftBy6Exact lowJ16 = refl
regularShiftBy6Exact lowJ17 = refl
regularShiftBy6Exact lowJ18 = refl
regularShiftBy6Exact lowJ19 = refl
regularShiftBy6Exact lowJ20 = refl
regularShiftBy6Exact lowJ21 = refl
regularShiftBy6Exact lowJ22 = refl
regularShiftBy6Exact lowJ23 = refl
regularShiftBy6Exact lowJ24 = refl
regularShiftBy6Exact lowJ25 = refl
regularShiftBy6Exact lowJ26 = refl
regularShiftBy6Exact lowJ27 = refl
regularShiftBy6Exact lowJ28 = refl
regularShiftBy6Exact lowJ29 = refl

j1ToJ7IsOneRegularShift :
  branchingSpectrum Spin.j7
  ≡ addSpectrum regularSpectrum (branchingSpectrum Spin.j1)
j1ToJ7IsOneRegularShift = refl

tetrahedralOrder tetrahedralPeriod : Nat
tetrahedralOrder = 12
tetrahedralPeriod = 6

twicePeriodIsOrder : 2 * tetrahedralPeriod ≡ tetrahedralOrder
twicePeriodIsOrder = refl

------------------------------------------------------------------------
-- Character reconstruction; the source SO(3) character is real on both C3
-- classes while the two one-dimensional A4 characters are conjugate.
------------------------------------------------------------------------

branchingCharacter : TetrahedralSpectrum → TetrahedralClass → EisensteinInt
branchingCharacter spectrum class =
  addE
    (scaleE (multiplicityT1 spectrum) (irrepCharacter T1 class))
    (addE
      (scaleE (multiplicityT1Omega spectrum) (irrepCharacter T1Omega class))
      (addE
        (scaleE
          (multiplicityT1OmegaSquared spectrum)
          (irrepCharacter T1OmegaSquared class))
        (scaleE (multiplicityT3 spectrum) (irrepCharacter T3 class))))

restrictedCharacter : Spin.AngularMomentum0To35 → TetrahedralClass → EisensteinInt
restrictedCharacter j identityClass = integerE (+ (Spin.jDimension j))
restrictedCharacter j halfTurnClass = integerE (Fixed.halfTurnCharacter (Spin.jNat j))
restrictedCharacter j thirdTurnClass = integerE (Fixed.thirdTurnCharacter (Spin.jNat j))
restrictedCharacter j thirdTurnInverseClass = integerE (Fixed.thirdTurnCharacter (Spin.jNat j))

record TetrahedralRestrictionBoundary : Set where
  field
    exactBranchingJ0To35Constructed : Bool
    exactBranchingJ0To35ConstructedIsTrue : exactBranchingJ0To35Constructed ≡ true
    conjugateOneDimensionalSpeciesKeptSeparate : Bool
    conjugateOneDimensionalSpeciesKeptSeparateIsTrue : conjugateOneDimensionalSpeciesKeptSeparate ≡ true
    regularQuotientPeriodSixProvedOnScan : Bool
    regularQuotientPeriodSixProvedOnScanIsTrue : regularQuotientPeriodSixProvedOnScan ≡ true
    fixedA4QuotientClaimedToCharacterizeOgg : Bool
    fixedA4QuotientClaimedToCharacterizeOggIsFalse : fixedA4QuotientClaimedToCharacterizeOgg ≡ false

canonicalTetrahedralRestrictionBoundary : TetrahedralRestrictionBoundary
canonicalTetrahedralRestrictionBoundary =
  record
    { exactBranchingJ0To35Constructed = true
    ; exactBranchingJ0To35ConstructedIsTrue = refl
    ; conjugateOneDimensionalSpeciesKeptSeparate = true
    ; conjugateOneDimensionalSpeciesKeptSeparateIsTrue = refl
    ; regularQuotientPeriodSixProvedOnScan = true
    ; regularQuotientPeriodSixProvedOnScanIsTrue = refl
    ; fixedA4QuotientClaimedToCharacterizeOgg = false
    ; fixedA4QuotientClaimedToCharacterizeOggIsFalse = refl
    }
