module DASHI.Moonshine.P11ClassicalCharacteristicHeckeInstanceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Reinier Bröker, Kristin Lauter and Andrew V. Sutherland,
-- "Modular polynomials via isogeny volcanoes",
-- Mathematics of Computation 81 (2012), 1201--1231.
-- DOI: 10.1090/S0025-5718-2011-02508-1.
--
-- DASHI CONTRIBUTION
--
-- Package the exact p=11, ell=2 modular-polynomial correspondence as the first
-- inhabitant of the corrected two-index classical Hecke family.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.ClassicalCharacteristicHeckeFamilyCore as Family
import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11

P11CarrierFamily : Nat → Set
P11CarrierFamily characteristic = P11.J11Class

P11Admissible : Nat → Nat → Set
P11Admissible characteristic heckeDegree =
  (characteristic ≡ 11) × (heckeDegree ≡ 2)

p11ClassicalFamily : Family.ClassicalCharacteristicHeckeFamily P11CarrierFamily
p11ClassicalFamily =
  record
    { Admissible = P11Admissible
    ; correspondence = λ characteristic heckeDegree admissible →
        P11.p11TwoIsogenyCorrespondence
    ; degreeMatchesIndex = λ characteristic heckeDegree admissible →
        degreeMatch characteristic heckeDegree admissible
    }
  where
    degreeMatch :
      (characteristic heckeDegree : Nat) →
      P11Admissible characteristic heckeDegree →
      2 ≡ heckeDegree
    degreeMatch characteristic heckeDegree (characteristicIs11 , heckeIs2) =
      sym heckeIs2

p11Ell2IsAdmissible : P11Admissible 11 2
p11Ell2IsAdmissible = refl , refl

p11FamilyReturnsExactCorrespondence :
  Family.correspondence p11ClassicalFamily 11 2 p11Ell2IsAdmissible
  ≡ P11.p11TwoIsogenyCorrespondence
p11FamilyReturnsExactCorrespondence = refl

p11FamilyDegreeIsTwo :
  Family.degreeMatchesIndex p11ClassicalFamily 11 2 p11Ell2IsAdmissible
  ≡ refl
p11FamilyDegreeIsTwo = refl
