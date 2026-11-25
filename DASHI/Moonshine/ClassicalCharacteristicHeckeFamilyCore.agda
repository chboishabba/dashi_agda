module DASHI.Moonshine.ClassicalCharacteristicHeckeFamilyCore where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- Reinier Bröker, Kristin Lauter and Andrew V. Sutherland,
-- "Modular polynomials via isogeny volcanoes",
-- Mathematics of Computation 81 (2012), 1201--1231.
-- DOI: 10.1090/S0025-5718-2011-02508-1.
--
-- DASHI CONTRIBUTION
--
-- Correct an index conflation in the older finite Hecke ontology lane.
--
-- For supersingular/Brandt geometry there are two independent prime roles:
--
--   p   : characteristic / level selecting the state space S_p;
--   ell : Hecke/isogeny degree selecting an ell+1 neighbour correspondence
--         on that same state space (normally with ell != p).
--
-- The existing PrimeCorrespondenceHeckeOn has one SSP index and a fixed Vec15
-- fibre, so it is retained as an ontology-level model rather than identified
-- with this classical two-index family.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical

record ClassicalCharacteristicHeckeFamily
    (Class : Nat → Set) : Set₁ where
  field
    Admissible : Nat → Nat → Set

    correspondence :
      (characteristic heckeDegree : Nat) →
      Admissible characteristic heckeDegree →
      Classical.ClassicalPrimeDegreeCorrespondence (Class characteristic)

    degreeMatchesIndex :
      (characteristic heckeDegree : Nat) →
      (admissible : Admissible characteristic heckeDegree) →
      Classical.degreePrime
        (correspondence characteristic heckeDegree admissible)
      ≡ heckeDegree

open ClassicalCharacteristicHeckeFamily public

record ClassicalCharacteristicHeckeBoundary : Set where
  field
    characteristicAndHeckeDegreeSeparated : Bool
    characteristicAndHeckeDegreeSeparatedIsTrue :
      characteristicAndHeckeDegreeSeparated ≡ true

    stateCarrierMayDependOnCharacteristic : Bool
    stateCarrierMayDependOnCharacteristicIsTrue :
      stateCarrierMayDependOnCharacteristic ≡ true

    correspondenceDegreeMayDependOnHeckePrime : Bool
    correspondenceDegreeMayDependOnHeckePrimeIsTrue :
      correspondenceDegreeMayDependOnHeckePrime ≡ true

    oldSingleSSPIndexDeclaredClassicallyEquivalent : Bool
    oldSingleSSPIndexDeclaredClassicallyEquivalentIsFalse :
      oldSingleSSPIndexDeclaredClassicallyEquivalent ≡ false

canonicalClassicalCharacteristicHeckeBoundary :
  ClassicalCharacteristicHeckeBoundary
canonicalClassicalCharacteristicHeckeBoundary =
  record
    { characteristicAndHeckeDegreeSeparated = true
    ; characteristicAndHeckeDegreeSeparatedIsTrue = refl
    ; stateCarrierMayDependOnCharacteristic = true
    ; stateCarrierMayDependOnCharacteristicIsTrue = refl
    ; correspondenceDegreeMayDependOnHeckePrime = true
    ; correspondenceDegreeMayDependOnHeckePrimeIsTrue = refl
    ; oldSingleSSPIndexDeclaredClassicallyEquivalent = false
    ; oldSingleSSPIndexDeclaredClassicallyEquivalentIsFalse = refl
    }
