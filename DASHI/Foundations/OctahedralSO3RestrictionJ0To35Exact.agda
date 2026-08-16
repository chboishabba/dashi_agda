module DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact where

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
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Restrict the SO(3) angular-momentum characters V_j, j=0..35, to the
-- rotational octahedral group O ~= S4. The five finite irreps are the cubic
-- A1, A2, E, T1, T2 carriers of dimensions 1,1,2,3,3.
--
-- The calculation is exact and deliberately includes non-Ogg dimensions.
-- Its strongest control law is
--
--   Res_O V_(j+12) = Res_O V_j + Reg_O
--
-- on the scanned range. Consequently a selector that sees only the branching
-- class modulo regular representation cannot characterize the Ogg list.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Foundations.FiniteRepresentationRestrictionCore as Core
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin

data OctahedralIrrep : Set where
  A1 A2 E T1 T2 : OctahedralIrrep

octahedralIrrepDimension : OctahedralIrrep → Nat
octahedralIrrepDimension A1 = 1
octahedralIrrepDimension A2 = 1
octahedralIrrepDimension E = 2
octahedralIrrepDimension T1 = 3
octahedralIrrepDimension T2 = 3

allOctahedralIrreps : List OctahedralIrrep
allOctahedralIrreps = A1 ∷ A2 ∷ E ∷ T1 ∷ T2 ∷ []

octahedralFamily : Core.FiniteIrrepFamily
octahedralFamily =
  Core.finite-irrep-family
    OctahedralIrrep
    allOctahedralIrreps
    octahedralIrrepDimension
    "rotational octahedral group O ~= S4; irreps A1,A2,E,T1,T2"

data OctahedralClass : Set where
  identityClass edgeHalfTurnClass faceHalfTurnClass thirdTurnClass quarterTurnClass : OctahedralClass

irrepCharacter : OctahedralIrrep → OctahedralClass → ℤ
irrepCharacter A1 identityClass = + 1
irrepCharacter A1 edgeHalfTurnClass = + 1
irrepCharacter A1 faceHalfTurnClass = + 1
irrepCharacter A1 thirdTurnClass = + 1
irrepCharacter A1 quarterTurnClass = + 1
irrepCharacter A2 identityClass = + 1
irrepCharacter A2 edgeHalfTurnClass = -[1+ 0 ]
irrepCharacter A2 faceHalfTurnClass = + 1
irrepCharacter A2 thirdTurnClass = + 1
irrepCharacter A2 quarterTurnClass = -[1+ 0 ]
irrepCharacter E identityClass = + 2
irrepCharacter E edgeHalfTurnClass = + 0
irrepCharacter E faceHalfTurnClass = + 2
irrepCharacter E thirdTurnClass = -[1+ 0 ]
irrepCharacter E quarterTurnClass = + 0
irrepCharacter T1 identityClass = + 3
irrepCharacter T1 edgeHalfTurnClass = -[1+ 0 ]
irrepCharacter T1 faceHalfTurnClass = -[1+ 0 ]
irrepCharacter T1 thirdTurnClass = + 0
irrepCharacter T1 quarterTurnClass = + 1
irrepCharacter T2 identityClass = + 3
irrepCharacter T2 edgeHalfTurnClass = + 1
irrepCharacter T2 faceHalfTurnClass = -[1+ 0 ]
irrepCharacter T2 thirdTurnClass = + 0
irrepCharacter T2 quarterTurnClass = -[1+ 0 ]

record OctahedralSpectrum : Set where
  constructor oct-spectrum
  field
    multiplicityA1 multiplicityA2 multiplicityE multiplicityT1 multiplicityT2 : Nat

open OctahedralSpectrum public

multiplicityOf : OctahedralSpectrum → OctahedralIrrep → Nat
multiplicityOf spectrum A1 = multiplicityA1 spectrum
multiplicityOf spectrum A2 = multiplicityA2 spectrum
multiplicityOf spectrum E = multiplicityE spectrum
multiplicityOf spectrum T1 = multiplicityT1 spectrum
multiplicityOf spectrum T2 = multiplicityT2 spectrum

branchingDimension : OctahedralSpectrum → Nat
branchingDimension spectrum =
  Core.sumWeighted allOctahedralIrreps octahedralIrrepDimension (multiplicityOf spectrum)

branchingSpectrum : Spin.AngularMomentum0To35 → OctahedralSpectrum
branchingSpectrum Spin.j0 = oct-spectrum 1 0 0 0 0
branchingSpectrum Spin.j1 = oct-spectrum 0 0 0 1 0
branchingSpectrum Spin.j2 = oct-spectrum 0 0 1 0 1
branchingSpectrum Spin.j3 = oct-spectrum 0 1 0 1 1
branchingSpectrum Spin.j4 = oct-spectrum 1 0 1 1 1
branchingSpectrum Spin.j5 = oct-spectrum 0 0 1 2 1
branchingSpectrum Spin.j6 = oct-spectrum 1 1 1 1 2
branchingSpectrum Spin.j7 = oct-spectrum 0 1 1 2 2
branchingSpectrum Spin.j8 = oct-spectrum 1 0 2 2 2
branchingSpectrum Spin.j9 = oct-spectrum 1 1 1 3 2
branchingSpectrum Spin.j10 = oct-spectrum 1 1 2 2 3
branchingSpectrum Spin.j11 = oct-spectrum 0 1 2 3 3
branchingSpectrum Spin.j12 = oct-spectrum 2 1 2 3 3
branchingSpectrum Spin.j13 = oct-spectrum 1 1 2 4 3
branchingSpectrum Spin.j14 = oct-spectrum 1 1 3 3 4
branchingSpectrum Spin.j15 = oct-spectrum 1 2 2 4 4
branchingSpectrum Spin.j16 = oct-spectrum 2 1 3 4 4
branchingSpectrum Spin.j17 = oct-spectrum 1 1 3 5 4
branchingSpectrum Spin.j18 = oct-spectrum 2 2 3 4 5
branchingSpectrum Spin.j19 = oct-spectrum 1 2 3 5 5
branchingSpectrum Spin.j20 = oct-spectrum 2 1 4 5 5
branchingSpectrum Spin.j21 = oct-spectrum 2 2 3 6 5
branchingSpectrum Spin.j22 = oct-spectrum 2 2 4 5 6
branchingSpectrum Spin.j23 = oct-spectrum 1 2 4 6 6
branchingSpectrum Spin.j24 = oct-spectrum 3 2 4 6 6
branchingSpectrum Spin.j25 = oct-spectrum 2 2 4 7 6
branchingSpectrum Spin.j26 = oct-spectrum 2 2 5 6 7
branchingSpectrum Spin.j27 = oct-spectrum 2 3 4 7 7
branchingSpectrum Spin.j28 = oct-spectrum 3 2 5 7 7
branchingSpectrum Spin.j29 = oct-spectrum 2 2 5 8 7
branchingSpectrum Spin.j30 = oct-spectrum 3 3 5 7 8
branchingSpectrum Spin.j31 = oct-spectrum 2 3 5 8 8
branchingSpectrum Spin.j32 = oct-spectrum 3 2 6 8 8
branchingSpectrum Spin.j33 = oct-spectrum 3 3 5 9 8
branchingSpectrum Spin.j34 = oct-spectrum 3 3 6 8 9
branchingSpectrum Spin.j35 = oct-spectrum 2 3 6 9 9

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

octahedralBranching :
  (j : Spin.AngularMomentum0To35) →
  Core.BranchingSpectrum (Spin.continuousSO3Irrep j) octahedralFamily
octahedralBranching j =
  Core.branching-spectrum
    (multiplicityOf (branchingSpectrum j))
    (branchingDimensionExact j)
    "exact rotational-octahedral restriction on the j=0..35 control scan"

regularSpectrum : OctahedralSpectrum
regularSpectrum = oct-spectrum 1 1 2 3 3

addSpectrum : OctahedralSpectrum → OctahedralSpectrum → OctahedralSpectrum
addSpectrum left right =
  oct-spectrum
    (multiplicityA1 left + multiplicityA1 right)
    (multiplicityA2 left + multiplicityA2 right)
    (multiplicityE left + multiplicityE right)
    (multiplicityT1 left + multiplicityT1 right)
    (multiplicityT2 left + multiplicityT2 right)

data LowJ0To23 : Set where
  lowJ0 lowJ1 lowJ2 lowJ3 lowJ4 lowJ5 lowJ6 lowJ7 lowJ8 lowJ9 lowJ10 lowJ11 lowJ12 lowJ13 lowJ14 lowJ15 lowJ16 lowJ17 lowJ18 lowJ19 lowJ20 lowJ21 lowJ22 lowJ23 : LowJ0To23

embedLowJ : LowJ0To23 → Spin.AngularMomentum0To35
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

shiftLowJBy12 : LowJ0To23 → Spin.AngularMomentum0To35
shiftLowJBy12 lowJ0 = Spin.j12
shiftLowJBy12 lowJ1 = Spin.j13
shiftLowJBy12 lowJ2 = Spin.j14
shiftLowJBy12 lowJ3 = Spin.j15
shiftLowJBy12 lowJ4 = Spin.j16
shiftLowJBy12 lowJ5 = Spin.j17
shiftLowJBy12 lowJ6 = Spin.j18
shiftLowJBy12 lowJ7 = Spin.j19
shiftLowJBy12 lowJ8 = Spin.j20
shiftLowJBy12 lowJ9 = Spin.j21
shiftLowJBy12 lowJ10 = Spin.j22
shiftLowJBy12 lowJ11 = Spin.j23
shiftLowJBy12 lowJ12 = Spin.j24
shiftLowJBy12 lowJ13 = Spin.j25
shiftLowJBy12 lowJ14 = Spin.j26
shiftLowJBy12 lowJ15 = Spin.j27
shiftLowJBy12 lowJ16 = Spin.j28
shiftLowJBy12 lowJ17 = Spin.j29
shiftLowJBy12 lowJ18 = Spin.j30
shiftLowJBy12 lowJ19 = Spin.j31
shiftLowJBy12 lowJ20 = Spin.j32
shiftLowJBy12 lowJ21 = Spin.j33
shiftLowJBy12 lowJ22 = Spin.j34
shiftLowJBy12 lowJ23 = Spin.j35

regularShiftBy12Exact :
  (j : LowJ0To23) →
  branchingSpectrum (shiftLowJBy12 j)
  ≡ addSpectrum regularSpectrum (branchingSpectrum (embedLowJ j))
regularShiftBy12Exact lowJ0 = refl
regularShiftBy12Exact lowJ1 = refl
regularShiftBy12Exact lowJ2 = refl
regularShiftBy12Exact lowJ3 = refl
regularShiftBy12Exact lowJ4 = refl
regularShiftBy12Exact lowJ5 = refl
regularShiftBy12Exact lowJ6 = refl
regularShiftBy12Exact lowJ7 = refl
regularShiftBy12Exact lowJ8 = refl
regularShiftBy12Exact lowJ9 = refl
regularShiftBy12Exact lowJ10 = refl
regularShiftBy12Exact lowJ11 = refl
regularShiftBy12Exact lowJ12 = refl
regularShiftBy12Exact lowJ13 = refl
regularShiftBy12Exact lowJ14 = refl
regularShiftBy12Exact lowJ15 = refl
regularShiftBy12Exact lowJ16 = refl
regularShiftBy12Exact lowJ17 = refl
regularShiftBy12Exact lowJ18 = refl
regularShiftBy12Exact lowJ19 = refl
regularShiftBy12Exact lowJ20 = refl
regularShiftBy12Exact lowJ21 = refl
regularShiftBy12Exact lowJ22 = refl
regularShiftBy12Exact lowJ23 = refl

j2ToJ26IsTwoRegularShifts :
  branchingSpectrum Spin.j26
  ≡ addSpectrum regularSpectrum
      (addSpectrum regularSpectrum (branchingSpectrum Spin.j2))
j2ToJ26IsTwoRegularShifts = refl

data AtMostOne : Nat → Set where
  zeroAtMostOne : AtMostOne 0
  oneAtMostOne : AtMostOne 1

record MultiplicityFree (spectrum : OctahedralSpectrum) : Set where
  field
    a1AtMostOne : AtMostOne (multiplicityA1 spectrum)
    a2AtMostOne : AtMostOne (multiplicityA2 spectrum)
    eAtMostOne : AtMostOne (multiplicityE spectrum)
    t1AtMostOne : AtMostOne (multiplicityT1 spectrum)
    t2AtMostOne : AtMostOne (multiplicityT2 spectrum)

j3SevenIsMultiplicityFree : MultiplicityFree (branchingSpectrum Spin.j3)
j3SevenIsMultiplicityFree =
  record
    { a1AtMostOne = zeroAtMostOne
    ; a2AtMostOne = oneAtMostOne
    ; eAtMostOne = zeroAtMostOne
    ; t1AtMostOne = oneAtMostOne
    ; t2AtMostOne = oneAtMostOne
    }

j4NineIsMultiplicityFree : MultiplicityFree (branchingSpectrum Spin.j4)
j4NineIsMultiplicityFree =
  record
    { a1AtMostOne = oneAtMostOne
    ; a2AtMostOne = zeroAtMostOne
    ; eAtMostOne = oneAtMostOne
    ; t1AtMostOne = oneAtMostOne
    ; t2AtMostOne = oneAtMostOne
    }

j4NineBranching : branchingSpectrum Spin.j4 ≡ oct-spectrum 1 0 1 1 1
j4NineBranching = refl

record OctahedralRestrictionBoundary : Set where
  field
    exactBranchingJ0To35Constructed : Bool
    exactBranchingJ0To35ConstructedIsTrue : exactBranchingJ0To35Constructed ≡ true
    allDimensionsComputedWithoutOggFilter : Bool
    allDimensionsComputedWithoutOggFilterIsTrue : allDimensionsComputedWithoutOggFilter ≡ true
    regularQuotientPeriodTwelveProvedOnScan : Bool
    regularQuotientPeriodTwelveProvedOnScanIsTrue : regularQuotientPeriodTwelveProvedOnScan ≡ true
    cleanBranchingClaimedToCharacterizeOgg : Bool
    cleanBranchingClaimedToCharacterizeOggIsFalse : cleanBranchingClaimedToCharacterizeOgg ≡ false

canonicalOctahedralRestrictionBoundary : OctahedralRestrictionBoundary
canonicalOctahedralRestrictionBoundary =
  record
    { exactBranchingJ0To35Constructed = true
    ; exactBranchingJ0To35ConstructedIsTrue = refl
    ; allDimensionsComputedWithoutOggFilter = true
    ; allDimensionsComputedWithoutOggFilterIsTrue = refl
    ; regularQuotientPeriodTwelveProvedOnScan = true
    ; regularQuotientPeriodTwelveProvedOnScanIsTrue = refl
    ; cleanBranchingClaimedToCharacterizeOgg = false
    ; cleanBranchingClaimedToCharacterizeOggIsFalse = refl
    }
