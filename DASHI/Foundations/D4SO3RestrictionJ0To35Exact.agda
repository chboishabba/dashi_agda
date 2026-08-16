module DASHI.Foundations.D4SO3RestrictionJ0To35Exact where

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
-- Compute the rotational-D4 branching spectrum for every j=0..35 without an
-- Ogg filter.  The exact finite recurrence is
--
--   Res_D4 V_(j+4) = Res_D4 V_j + Reg_D4.
--
-- Since |D4|=8=2*4, the dimension increment across one nonidentity-character
-- period is exactly the regular-representation dimension.  In particular
--
--   V_4 | D4 = A1 + Reg_D4
--
-- and therefore its nine dimensions contain all five D4 irrep species.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin

record D4Spectrum : Set where
  constructor d4-spectrum
  field
    multiplicityA1 multiplicityA2 multiplicityB1 multiplicityB2 multiplicityE : Nat

open D4Spectrum public

branchingSpectrum : Spin.AngularMomentum0To35 → D4Spectrum
branchingSpectrum Spin.j0 = d4-spectrum 1 0 0 0 0
branchingSpectrum Spin.j1 = d4-spectrum 0 1 0 0 1
branchingSpectrum Spin.j2 = d4-spectrum 1 0 1 1 1
branchingSpectrum Spin.j3 = d4-spectrum 0 1 1 1 2
branchingSpectrum Spin.j4 = d4-spectrum 2 1 1 1 2
branchingSpectrum Spin.j5 = d4-spectrum 1 2 1 1 3
branchingSpectrum Spin.j6 = d4-spectrum 2 1 2 2 3
branchingSpectrum Spin.j7 = d4-spectrum 1 2 2 2 4
branchingSpectrum Spin.j8 = d4-spectrum 3 2 2 2 4
branchingSpectrum Spin.j9 = d4-spectrum 2 3 2 2 5
branchingSpectrum Spin.j10 = d4-spectrum 3 2 3 3 5
branchingSpectrum Spin.j11 = d4-spectrum 2 3 3 3 6
branchingSpectrum Spin.j12 = d4-spectrum 4 3 3 3 6
branchingSpectrum Spin.j13 = d4-spectrum 3 4 3 3 7
branchingSpectrum Spin.j14 = d4-spectrum 4 3 4 4 7
branchingSpectrum Spin.j15 = d4-spectrum 3 4 4 4 8
branchingSpectrum Spin.j16 = d4-spectrum 5 4 4 4 8
branchingSpectrum Spin.j17 = d4-spectrum 4 5 4 4 9
branchingSpectrum Spin.j18 = d4-spectrum 5 4 5 5 9
branchingSpectrum Spin.j19 = d4-spectrum 4 5 5 5 10
branchingSpectrum Spin.j20 = d4-spectrum 6 5 5 5 10
branchingSpectrum Spin.j21 = d4-spectrum 5 6 5 5 11
branchingSpectrum Spin.j22 = d4-spectrum 6 5 6 6 11
branchingSpectrum Spin.j23 = d4-spectrum 5 6 6 6 12
branchingSpectrum Spin.j24 = d4-spectrum 7 6 6 6 12
branchingSpectrum Spin.j25 = d4-spectrum 6 7 6 6 13
branchingSpectrum Spin.j26 = d4-spectrum 7 6 7 7 13
branchingSpectrum Spin.j27 = d4-spectrum 6 7 7 7 14
branchingSpectrum Spin.j28 = d4-spectrum 8 7 7 7 14
branchingSpectrum Spin.j29 = d4-spectrum 7 8 7 7 15
branchingSpectrum Spin.j30 = d4-spectrum 8 7 8 8 15
branchingSpectrum Spin.j31 = d4-spectrum 7 8 8 8 16
branchingSpectrum Spin.j32 = d4-spectrum 9 8 8 8 16
branchingSpectrum Spin.j33 = d4-spectrum 8 9 8 8 17
branchingSpectrum Spin.j34 = d4-spectrum 9 8 9 9 17
branchingSpectrum Spin.j35 = d4-spectrum 8 9 9 9 18

multiplicityOf : D4Spectrum → Candidate.D4IrrepKind → Nat
multiplicityOf spectrum Candidate.A1 = multiplicityA1 spectrum
multiplicityOf spectrum Candidate.A2 = multiplicityA2 spectrum
multiplicityOf spectrum Candidate.B1 = multiplicityB1 spectrum
multiplicityOf spectrum Candidate.B2 = multiplicityB2 spectrum
multiplicityOf spectrum Candidate.E2 = multiplicityE spectrum

branchingDimension : D4Spectrum → Nat
branchingDimension spectrum =
  multiplicityA1 spectrum
  + multiplicityA2 spectrum
  + multiplicityB1 spectrum
  + multiplicityB2 spectrum
  + 2 * multiplicityE spectrum

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

regularSpectrum : D4Spectrum
regularSpectrum = d4-spectrum 1 1 1 1 2

addSpectrum : D4Spectrum → D4Spectrum → D4Spectrum
addSpectrum left right =
  d4-spectrum
    (multiplicityA1 left + multiplicityA1 right)
    (multiplicityA2 left + multiplicityA2 right)
    (multiplicityB1 left + multiplicityB1 right)
    (multiplicityB2 left + multiplicityB2 right)
    (multiplicityE left + multiplicityE right)

data LowJ0To31 : Set where
  lowJ0 lowJ1 lowJ2 lowJ3 lowJ4 lowJ5 lowJ6 lowJ7 lowJ8 lowJ9 lowJ10 lowJ11 lowJ12 lowJ13 lowJ14 lowJ15 lowJ16 lowJ17 lowJ18 lowJ19 lowJ20 lowJ21 lowJ22 lowJ23 lowJ24 lowJ25 lowJ26 lowJ27 lowJ28 lowJ29 lowJ30 lowJ31 : LowJ0To31

embedLowJ : LowJ0To31 → Spin.AngularMomentum0To35
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
embedLowJ lowJ30 = Spin.j30
embedLowJ lowJ31 = Spin.j31

shiftLowJBy4 : LowJ0To31 → Spin.AngularMomentum0To35
shiftLowJBy4 lowJ0 = Spin.j4
shiftLowJBy4 lowJ1 = Spin.j5
shiftLowJBy4 lowJ2 = Spin.j6
shiftLowJBy4 lowJ3 = Spin.j7
shiftLowJBy4 lowJ4 = Spin.j8
shiftLowJBy4 lowJ5 = Spin.j9
shiftLowJBy4 lowJ6 = Spin.j10
shiftLowJBy4 lowJ7 = Spin.j11
shiftLowJBy4 lowJ8 = Spin.j12
shiftLowJBy4 lowJ9 = Spin.j13
shiftLowJBy4 lowJ10 = Spin.j14
shiftLowJBy4 lowJ11 = Spin.j15
shiftLowJBy4 lowJ12 = Spin.j16
shiftLowJBy4 lowJ13 = Spin.j17
shiftLowJBy4 lowJ14 = Spin.j18
shiftLowJBy4 lowJ15 = Spin.j19
shiftLowJBy4 lowJ16 = Spin.j20
shiftLowJBy4 lowJ17 = Spin.j21
shiftLowJBy4 lowJ18 = Spin.j22
shiftLowJBy4 lowJ19 = Spin.j23
shiftLowJBy4 lowJ20 = Spin.j24
shiftLowJBy4 lowJ21 = Spin.j25
shiftLowJBy4 lowJ22 = Spin.j26
shiftLowJBy4 lowJ23 = Spin.j27
shiftLowJBy4 lowJ24 = Spin.j28
shiftLowJBy4 lowJ25 = Spin.j29
shiftLowJBy4 lowJ26 = Spin.j30
shiftLowJBy4 lowJ27 = Spin.j31
shiftLowJBy4 lowJ28 = Spin.j32
shiftLowJBy4 lowJ29 = Spin.j33
shiftLowJBy4 lowJ30 = Spin.j34
shiftLowJBy4 lowJ31 = Spin.j35

regularShiftBy4Exact :
  (j : LowJ0To31) →
  branchingSpectrum (shiftLowJBy4 j)
  ≡ addSpectrum regularSpectrum (branchingSpectrum (embedLowJ j))
regularShiftBy4Exact lowJ0 = refl
regularShiftBy4Exact lowJ1 = refl
regularShiftBy4Exact lowJ2 = refl
regularShiftBy4Exact lowJ3 = refl
regularShiftBy4Exact lowJ4 = refl
regularShiftBy4Exact lowJ5 = refl
regularShiftBy4Exact lowJ6 = refl
regularShiftBy4Exact lowJ7 = refl
regularShiftBy4Exact lowJ8 = refl
regularShiftBy4Exact lowJ9 = refl
regularShiftBy4Exact lowJ10 = refl
regularShiftBy4Exact lowJ11 = refl
regularShiftBy4Exact lowJ12 = refl
regularShiftBy4Exact lowJ13 = refl
regularShiftBy4Exact lowJ14 = refl
regularShiftBy4Exact lowJ15 = refl
regularShiftBy4Exact lowJ16 = refl
regularShiftBy4Exact lowJ17 = refl
regularShiftBy4Exact lowJ18 = refl
regularShiftBy4Exact lowJ19 = refl
regularShiftBy4Exact lowJ20 = refl
regularShiftBy4Exact lowJ21 = refl
regularShiftBy4Exact lowJ22 = refl
regularShiftBy4Exact lowJ23 = refl
regularShiftBy4Exact lowJ24 = refl
regularShiftBy4Exact lowJ25 = refl
regularShiftBy4Exact lowJ26 = refl
regularShiftBy4Exact lowJ27 = refl
regularShiftBy4Exact lowJ28 = refl
regularShiftBy4Exact lowJ29 = refl
regularShiftBy4Exact lowJ30 = refl
regularShiftBy4Exact lowJ31 = refl

j4IsTrivialPlusRegular :
  branchingSpectrum Spin.j4
  ≡ addSpectrum regularSpectrum (branchingSpectrum Spin.j0)
j4IsTrivialPlusRegular = refl

d4Order d4Period : Nat
d4Order = 8
d4Period = 4

twiceD4PeriodIsGroupOrder : 2 * d4Period ≡ d4Order
twiceD4PeriodIsGroupOrder = refl
