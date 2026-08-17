module DASHI.Moonshine.P13OggOneClassHeckeControlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires", 1974/75, MR 417184; no DOI.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Use the existing exact p=13 supersingular orbit spectrum as a second Ogg
-- control.  It has one total slot, one Frobenius-fixed slot and zero paired
-- orbits.  On a one-state carrier an ell-prime positive correspondence is
-- forced to consist of ell+1 loops.  The weight-two prime-square residual then
-- has
--
--   (ell+1)^2 - ell = ell^2 + ell + 1
--
-- positive contributions, giving arities 7,13,31 for ell=2,3,5.
--
-- This is a normal-form consequence of the existing finite spectrum, not an
-- independent enumeration of supersingular elliptic curves in characteristic
-- 13; that stronger realization remains separately classified.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum

------------------------------------------------------------------------
-- One-state source-normal-form carrier.
------------------------------------------------------------------------

data P13Class : Set where
  p13Only : P13Class

p13Spectrum : Orbit.InvolutionOrbitSpectrum
p13Spectrum = Spectrum.supersingularOrbitSpectrum Matrix.prime13

p13FixedCountIsOne : Orbit.fixedOrbitCount p13Spectrum ≡ 1
p13FixedCountIsOne = refl

p13PairedCountIsZero : Orbit.pairedOrbitCount p13Spectrum ≡ 0
p13PairedCountIsZero = refl

p13TotalCountIsOne : Orbit.totalCarrierCount p13Spectrum ≡ 1
p13TotalCountIsOne = refl

p13Frobenius : P13Class → P13Class
p13Frobenius p13Only = p13Only

p13FrobeniusFixed : (x : P13Class) → p13Frobenius x ≡ x
p13FrobeniusFixed p13Only = refl

------------------------------------------------------------------------
-- Prime systems: every slot returns to the unique class.
------------------------------------------------------------------------

constantNeighbour : ∀ {n} → P13Class → Fin n → P13Class
constantNeighbour p13Only edge = p13Only

P13T2 : Positive.PositiveFiniteNeighbourSystem P13Class
P13T2 = record
  { Positive.arity = 3
  ; Positive.neighbour = constantNeighbour
  }

P13T3 : Positive.PositiveFiniteNeighbourSystem P13Class
P13T3 = record
  { Positive.arity = 4
  ; Positive.neighbour = constantNeighbour
  }

P13T5 : Positive.PositiveFiniteNeighbourSystem P13Class
P13T5 = record
  { Positive.arity = 6
  ; Positive.neighbour = constantNeighbour
  }

P13T4 : Positive.PositiveFiniteNeighbourSystem P13Class
P13T4 = record
  { Positive.arity = 7
  ; Positive.neighbour = constantNeighbour
  }

P13T9 : Positive.PositiveFiniteNeighbourSystem P13Class
P13T9 = record
  { Positive.arity = 13
  ; Positive.neighbour = constantNeighbour
  }

P13T25 : Positive.PositiveFiniteNeighbourSystem P13Class
P13T25 = record
  { Positive.arity = 31
  ; Positive.neighbour = constantNeighbour
  }

isOnly : P13Class → Nat
isOnly p13Only = 1

p13T2Degree : Positive.positiveOperator P13T2 isOnly p13Only ≡ 3
p13T2Degree = refl

p13T3Degree : Positive.positiveOperator P13T3 isOnly p13Only ≡ 4
p13T3Degree = refl

p13T5Degree : Positive.positiveOperator P13T5 isOnly p13Only ≡ 6
p13T5Degree = refl

p13T4Degree : Positive.positiveOperator P13T4 isOnly p13Only ≡ 7
p13T4Degree = refl

p13T9Degree : Positive.positiveOperator P13T9 isOnly p13Only ≡ 13
p13T9Degree = refl

p13T25Degree : Positive.positiveOperator P13T25 isOnly p13Only ≡ 31
p13T25Degree = refl

------------------------------------------------------------------------
-- Exact count form of the weight-two prime-square relations.
------------------------------------------------------------------------

p13T2SquareCount : 3 * 3 ≡ 7 + 2
p13T2SquareCount = refl

p13T3SquareCount : 4 * 4 ≡ 13 + 3
p13T3SquareCount = refl

p13T5SquareCount : 6 * 6 ≡ 31 + 5
p13T5SquareCount = refl

p13FiniteFrobeniusSelectorTrue :
  Spectrum.allSupersingularSlotsFixed Matrix.prime13 ≡ true
p13FiniteFrobeniusSelectorTrue = refl

record P13OggOneClassBoundary : Set where
  field
    oneStateNormalFormConstructed : Bool
    oneStateNormalFormConstructedIsTrue : oneStateNormalFormConstructed ≡ true

    positiveT2T3T5Constructed : Bool
    positiveT2T3T5ConstructedIsTrue : positiveT2T3T5Constructed ≡ true

    positivePrimeSquareCountsConstructed : Bool
    positivePrimeSquareCountsConstructedIsTrue :
      positivePrimeSquareCountsConstructed ≡ true

    frobeniusPairDefectZero : Bool
    frobeniusPairDefectZeroIsTrue : frobeniusPairDefectZero ≡ true

    independentP13EllipticCurveEnumerationConstructedHere : Bool
    independentP13EllipticCurveEnumerationConstructedHereIsFalse :
      independentP13EllipticCurveEnumerationConstructedHere ≡ false

canonicalP13OggOneClassBoundary : P13OggOneClassBoundary
canonicalP13OggOneClassBoundary = record
  { oneStateNormalFormConstructed = true
  ; oneStateNormalFormConstructedIsTrue = refl
  ; positiveT2T3T5Constructed = true
  ; positiveT2T3T5ConstructedIsTrue = refl
  ; positivePrimeSquareCountsConstructed = true
  ; positivePrimeSquareCountsConstructedIsTrue = refl
  ; frobeniusPairDefectZero = true
  ; frobeniusPairDefectZeroIsTrue = refl
  ; independentP13EllipticCurveEnumerationConstructedHere = false
  ; independentP13EllipticCurveEnumerationConstructedHereIsFalse = refl
  }
