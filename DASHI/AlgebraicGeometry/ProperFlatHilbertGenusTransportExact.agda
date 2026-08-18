module DASHI.AlgebraicGeometry.ProperFlatHilbertGenusTransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Robin Hartshorne,
-- "Algebraic Geometry", GTM 52, Springer, 1977.
-- DOI: 10.1007/978-1-4757-3849-0.
--
-- Chapter III, Section 9: in an appropriate flat projective/proper family the
-- Hilbert polynomial is constant on fibres.  For a proper curve, arithmetic
-- genus is determined by that Hilbert polynomial (equivalently by Euler
-- characteristic).
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact transport pattern without building a parallel scheme or
-- polynomial library.  A source-facing flat family supplies two actual fibre
-- Hilbert-polynomial objects in ONE carrier and the equality between them.
-- Arithmetic genus is a declared interpretation of that carrier.  Genus
-- equality is then derived by congruence; it is not an independent premise.
--
-- This is deliberately stronger bookkeeping than storing
--
--   genericGenus = specialGenus
--
-- as an opaque receipt, while remaining agnostic about the concrete polynomial
-- representation used by a future algebraic-geometry backend.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record ProperFlatHilbertGenusData : Set₁ where
  field
    HilbertPolynomial : Set
    arithmeticGenusOf : HilbertPolynomial → Nat

    genericHilbertPolynomial : HilbertPolynomial
    specialHilbertPolynomial : HilbertPolynomial

    flatHilbertPolynomialConstancy :
      genericHilbertPolynomial ≡ specialHilbertPolynomial

    genericGenus : Nat
    specialArithmeticGenus : Nat

    genericGenusFromHilbert :
      genericGenus ≡ arithmeticGenusOf genericHilbertPolynomial

    specialGenusFromHilbert :
      specialArithmeticGenus ≡ arithmeticGenusOf specialHilbertPolynomial

open ProperFlatHilbertGenusData public

hilbertArithmeticGenusTransport :
  (D : ProperFlatHilbertGenusData) →
  arithmeticGenusOf D (genericHilbertPolynomial D)
  ≡ arithmeticGenusOf D (specialHilbertPolynomial D)
hilbertArithmeticGenusTransport D =
  cong (arithmeticGenusOf D) (flatHilbertPolynomialConstancy D)

properFlatGenusTransport :
  (D : ProperFlatHilbertGenusData) →
  genericGenus D ≡ specialArithmeticGenus D
properFlatGenusTransport D =
  trans
    (genericGenusFromHilbert D)
    (trans
      (hilbertArithmeticGenusTransport D)
      (sym (specialGenusFromHilbert D)))

------------------------------------------------------------------------
-- Exact factorization: genus transport factors through Hilbert-polynomial
-- equality.  A consumer cannot supply genus equality without also supplying
-- the common polynomial carrier and fibre equality used here.
------------------------------------------------------------------------

record ProperFlatHilbertGenusTransportBoundary : Set where
  field
    commonHilbertPolynomialCarrierRequired : Bool
    flatPolynomialEqualityRequired : Bool
    arithmeticGenusInterpretationRequired : Bool
    genusTransportDerivedByCongruence : Bool
    schemeFlatnessConstructedHere : Bool
    concreteHilbertPolynomialBackendConstructedHere : Bool

canonicalProperFlatHilbertGenusTransportBoundary :
  ProperFlatHilbertGenusTransportBoundary
canonicalProperFlatHilbertGenusTransportBoundary = record
  { commonHilbertPolynomialCarrierRequired = true
  ; flatPolynomialEqualityRequired = true
  ; arithmeticGenusInterpretationRequired = true
  ; genusTransportDerivedByCongruence = true
  ; schemeFlatnessConstructedHere = false
  ; concreteHilbertPolynomialBackendConstructedHere = false
  }
