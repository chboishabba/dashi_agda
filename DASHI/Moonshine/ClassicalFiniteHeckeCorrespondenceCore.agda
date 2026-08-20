module DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore where

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
-- Separate the classical geometric prime-degree Hecke correspondence from the
-- repository's older Monster-prime Vec15 ontology correspondence.
--
-- For a prime degree ell, the classical modular polynomial Phi_ell has degree
-- ell+1 in the target variable: the fibre records the ell+1 cyclic order-ell
-- subgroups/quotients counted with multiplicity.  Therefore a classical finite
-- correspondence needs a variable-degree neighbour family, not a fixed Vec15.
--
-- This file gives only the finite carrier/algebra needed by explicit examples.
-- It does not construct modular curves or elliptic curves by itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

record ClassicalPrimeDegreeCorrespondence (Class : Set) : Set₁ where
  field
    degreePrime : Nat
    neighbour : Class → Fin (suc degreePrime) → Class

open ClassicalPrimeDegreeCorrespondence public

foldFin :
  ∀ {n : Nat} {A : Set} →
  (A → A → A) → A → (Fin n → A) → A
foldFin {zero} combine identity values = identity
foldFin {suc n} combine identity values =
  combine (values zero)
    (foldFin combine identity (λ index → values (suc index)))

classicalOperator :
  ∀ {Class : Set} →
  ClassicalPrimeDegreeCorrespondence Class →
  (Class → Nat) →
  Class → Nat
classicalOperator correspondence observable state =
  foldFin _+_ 0
    (λ index → observable (neighbour correspondence state index))

record ClassicalCorrespondenceBoundary : Set where
  field
    variablePrimeDegreeCarrierConstructed : Bool
    variablePrimeDegreeCarrierConstructedIsTrue :
      variablePrimeDegreeCarrierConstructed ≡ true

    fixedVec15IdentifiedWithClassicalHeckeFibre : Bool
    fixedVec15IdentifiedWithClassicalHeckeFibreIsFalse :
      fixedVec15IdentifiedWithClassicalHeckeFibre ≡ false

    modularPolynomialRealizationAutomatic : Bool
    modularPolynomialRealizationAutomaticIsFalse :
      modularPolynomialRealizationAutomatic ≡ false

canonicalClassicalCorrespondenceBoundary : ClassicalCorrespondenceBoundary
canonicalClassicalCorrespondenceBoundary =
  record
    { variablePrimeDegreeCarrierConstructed = true
    ; variablePrimeDegreeCarrierConstructedIsTrue = refl
    ; fixedVec15IdentifiedWithClassicalHeckeFibre = false
    ; fixedVec15IdentifiedWithClassicalHeckeFibreIsFalse = refl
    ; modularPolynomialRealizationAutomatic = false
    ; modularPolynomialRealizationAutomaticIsFalse = refl
    }
