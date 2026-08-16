module DASHI.Foundations.PolyhedralFixedSpaceDerivedNonaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Derive a 3/6/9-style address *after* actual representation reduction rather
-- than using nonary addressing as an SSP premise.
--
-- From the exact fixed-space spectrum take the pair
--
--   (dim V_j^C2 mod 3, dim V_j^C3 mod 3) in C3 x C3,
--
-- represented by the repository's TriTruth x TriTruth phase quotient Q9.  The
-- existing Q9 <-> NonaryTruth chart is then only a carrier presentation.
--
-- This diagnostic is intentionally lossy.  It has period 18 in j over the
-- scanned range, so j=3 (dimension 7) and j=21 (dimension 43) have the same
-- derived nonary address.  Since 7 is Ogg and 43 is not, this derived 369
-- coordinate cannot by itself be the SSP selector.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Nonary
import DASHI.Moonshine.OggPolyhedralReductionControlExact as Control
import MonsterOntos as Monster

fixedSpaceQ9 : Spin.AngularMomentum0To35 → Phase.PhaseQuotient9
fixedSpaceQ9 j =
  Base.fromTriIndex (Fixed.fixedDimension j Fixed.C2Probe)
  , Base.fromTriIndex (Fixed.fixedDimension j Fixed.C3Probe)

fixedSpaceNonary : Spin.AngularMomentum0To35 → Base.NonaryTruth
fixedSpaceNonary j = Nonary.phasePairToNonary (fixedSpaceQ9 j)

j3FixedQ9IsOrigin :
  fixedSpaceQ9 Spin.j3 ≡ (Base.tri-low , Base.tri-low)
j3FixedQ9IsOrigin = refl

j3FixedNonaryIsZero : fixedSpaceNonary Spin.j3 ≡ Base.non-0
j3FixedNonaryIsZero = refl

j21FixedNonaryIsZero : fixedSpaceNonary Spin.j21 ≡ Base.non-0
j21FixedNonaryIsZero = refl

j3AndJ21DerivedNonaryCollide :
  fixedSpaceNonary Spin.j3 ≡ fixedSpaceNonary Spin.j21
j3AndJ21DerivedNonaryCollide = refl

data LowJ0To17 : Set where
  lowJ0 lowJ1 lowJ2 lowJ3 lowJ4 lowJ5 lowJ6 lowJ7 lowJ8
    lowJ9 lowJ10 lowJ11 lowJ12 lowJ13 lowJ14 lowJ15 lowJ16 lowJ17 : LowJ0To17

embedLowJ : LowJ0To17 → Spin.AngularMomentum0To35
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

shiftLowJBy18 : LowJ0To17 → Spin.AngularMomentum0To35
shiftLowJBy18 lowJ0 = Spin.j18
shiftLowJBy18 lowJ1 = Spin.j19
shiftLowJBy18 lowJ2 = Spin.j20
shiftLowJBy18 lowJ3 = Spin.j21
shiftLowJBy18 lowJ4 = Spin.j22
shiftLowJBy18 lowJ5 = Spin.j23
shiftLowJBy18 lowJ6 = Spin.j24
shiftLowJBy18 lowJ7 = Spin.j25
shiftLowJBy18 lowJ8 = Spin.j26
shiftLowJBy18 lowJ9 = Spin.j27
shiftLowJBy18 lowJ10 = Spin.j28
shiftLowJBy18 lowJ11 = Spin.j29
shiftLowJBy18 lowJ12 = Spin.j30
shiftLowJBy18 lowJ13 = Spin.j31
shiftLowJBy18 lowJ14 = Spin.j32
shiftLowJBy18 lowJ15 = Spin.j33
shiftLowJBy18 lowJ16 = Spin.j34
shiftLowJBy18 lowJ17 = Spin.j35

derivedNonaryPeriod18OnScan :
  (j : LowJ0To17) →
  fixedSpaceNonary (shiftLowJBy18 j) ≡ fixedSpaceNonary (embedLowJ j)
derivedNonaryPeriod18OnScan lowJ0 = refl
derivedNonaryPeriod18OnScan lowJ1 = refl
derivedNonaryPeriod18OnScan lowJ2 = refl
derivedNonaryPeriod18OnScan lowJ3 = refl
derivedNonaryPeriod18OnScan lowJ4 = refl
derivedNonaryPeriod18OnScan lowJ5 = refl
derivedNonaryPeriod18OnScan lowJ6 = refl
derivedNonaryPeriod18OnScan lowJ7 = refl
derivedNonaryPeriod18OnScan lowJ8 = refl
derivedNonaryPeriod18OnScan lowJ9 = refl
derivedNonaryPeriod18OnScan lowJ10 = refl
derivedNonaryPeriod18OnScan lowJ11 = refl
derivedNonaryPeriod18OnScan lowJ12 = refl
derivedNonaryPeriod18OnScan lowJ13 = refl
derivedNonaryPeriod18OnScan lowJ14 = refl
derivedNonaryPeriod18OnScan lowJ15 = refl
derivedNonaryPeriod18OnScan lowJ16 = refl
derivedNonaryPeriod18OnScan lowJ17 = refl

dimension7IsOgg : Control.OggDimensionWitness 7
dimension7IsOgg = Monster.p7 , refl

dimension43IsNotOgg : Control.OggDimensionWitness 43 → ⊥
dimension43IsNotOgg (Monster.p2 , ())
dimension43IsNotOgg (Monster.p3 , ())
dimension43IsNotOgg (Monster.p5 , ())
dimension43IsNotOgg (Monster.p7 , ())
dimension43IsNotOgg (Monster.p11 , ())
dimension43IsNotOgg (Monster.p13 , ())
dimension43IsNotOgg (Monster.p17 , ())
dimension43IsNotOgg (Monster.p19 , ())
dimension43IsNotOgg (Monster.p23 , ())
dimension43IsNotOgg (Monster.p29 , ())
dimension43IsNotOgg (Monster.p31 , ())
dimension43IsNotOgg (Monster.p41 , ())
dimension43IsNotOgg (Monster.p47 , ())
dimension43IsNotOgg (Monster.p59 , ())
dimension43IsNotOgg (Monster.p71 , ())

record DerivedNonaryBoundary : Set where
  field
    nonaryDerivedFromFixedSpaces : Bool
    nonaryDerivedFromFixedSpacesIsTrue : nonaryDerivedFromFixedSpaces ≡ true
    nonaryUsedAsPrimitiveSSPSelector : Bool
    nonaryUsedAsPrimitiveSSPSelectorIsFalse : nonaryUsedAsPrimitiveSSPSelector ≡ false
    derivedCoordinateIsLossless : Bool
    derivedCoordinateIsLosslessIsFalse : derivedCoordinateIsLossless ≡ false
    derivedCoordinateAloneCharacterizesOgg : Bool
    derivedCoordinateAloneCharacterizesOggIsFalse : derivedCoordinateAloneCharacterizesOgg ≡ false

canonicalDerivedNonaryBoundary : DerivedNonaryBoundary
canonicalDerivedNonaryBoundary =
  record
    { nonaryDerivedFromFixedSpaces = true
    ; nonaryDerivedFromFixedSpacesIsTrue = refl
    ; nonaryUsedAsPrimitiveSSPSelector = false
    ; nonaryUsedAsPrimitiveSSPSelectorIsFalse = refl
    ; derivedCoordinateIsLossless = false
    ; derivedCoordinateIsLosslessIsFalse = refl
    ; derivedCoordinateAloneCharacterizesOgg = false
    ; derivedCoordinateAloneCharacterizesOggIsFalse = refl
    }
