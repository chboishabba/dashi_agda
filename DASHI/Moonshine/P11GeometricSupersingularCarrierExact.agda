module DASHI.Moonshine.P11GeometricSupersingularCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Supersingular elliptic curves", Chapter 42 of Quaternion Algebras,
-- Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4_42.
-- Book DOI: 10.1007/978-3-030-56694-4.
--
-- Voight's Example 42.3.11 gives the characteristic-11 case explicitly:
-- there are exactly two supersingular elliptic-curve classes, with j-invariants
-- 0 and 1728 = 1 mod 11.  The corresponding maximal-order unit groups have
-- orders 6 and 4 after matching the j=0 and j=1728 classes, so quotienting by
-- the central {+/-1} gives reduced automorphism orders 3 and 2.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition,
-- Graduate Texts in Mathematics 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
-- Chapter V, Example 4.3 likewise records that the supersingular j-invariants
-- in characteristic 11 are 0 and 1728 = 1.
--
-- DASHI CONTRIBUTION
--
-- Replace the previous anonymous two-slot Frobenius normal form by a typed,
-- source-certified geometric carrier whose constructors are the actual two
-- characteristic-11 supersingular j-classes.  This is an encoding of the cited
-- classical theorem, not a from-first-principles derivation of supersingularity
-- inside Agda's finite-field/elliptic-curve library.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11

------------------------------------------------------------------------
-- Actual characteristic-11 supersingular j-classes.
------------------------------------------------------------------------

data P11SupersingularJ : Set where
  jZeroSS : P11SupersingularJ
  j1728SS : P11SupersingularJ

jResidueMod11 : P11SupersingularJ → Nat
jResidueMod11 jZeroSS = 0
jResidueMod11 j1728SS = 1

j1728ResidueIsOne : jResidueMod11 j1728SS ≡ 1
j1728ResidueIsOne = refl

jZeroResidueIsZero : jResidueMod11 jZeroSS ≡ 0
jZeroResidueIsZero = refl

jZeroNotJ1728 : jZeroSS ≡ j1728SS → ⊥
jZeroNotJ1728 ()

------------------------------------------------------------------------
-- Explicit chart to the already-constructed modular-polynomial carrier.
------------------------------------------------------------------------

toP11Class : P11SupersingularJ → P11.J11Class
toP11Class jZeroSS = P11.j0
toP11Class j1728SS = P11.j1

fromP11Class : P11.J11Class → P11SupersingularJ
fromP11Class P11.j0 = jZeroSS
fromP11Class P11.j1 = j1728SS

fromAfterTo : (j : P11SupersingularJ) → fromP11Class (toP11Class j) ≡ j
fromAfterTo jZeroSS = refl
fromAfterTo j1728SS = refl

toAfterFrom : (j : P11.J11Class) → toP11Class (fromP11Class j) ≡ j
toAfterFrom P11.j0 = refl
toAfterFrom P11.j1 = refl

------------------------------------------------------------------------
-- Reduced automorphism orders |Aut(E)/{+/-1}|.
--
-- For j=0 the geometric automorphism group over the algebraic closure has
-- order 6, hence reduced order 3.  For j=1728 it has order 4, hence reduced
-- order 2.  These are the standard exceptional automorphism classes.
------------------------------------------------------------------------

reducedAutomorphismOrder : P11SupersingularJ → Nat
reducedAutomorphismOrder jZeroSS = 3
reducedAutomorphismOrder j1728SS = 2

jZeroReducedAutomorphismOrderIsThree :
  reducedAutomorphismOrder jZeroSS ≡ 3
jZeroReducedAutomorphismOrderIsThree = refl

j1728ReducedAutomorphismOrderIsTwo :
  reducedAutomorphismOrder j1728SS ≡ 2
j1728ReducedAutomorphismOrderIsTwo = refl

------------------------------------------------------------------------
-- Exhaustion is constructor-level because this carrier represents exactly the
-- two classes certified by the cited theorem.  We do not claim an independent
-- internal proof that an arbitrary elliptic curve over Fbar_11 is supersingular
-- iff its j-invariant is one of these constructors.
------------------------------------------------------------------------

record P11GeometricSupersingularBoundary : Set where
  field
    sourceCertifiedSupersingularCarrierConstructed : Bool
    sourceCertifiedSupersingularCarrierConstructedIsTrue :
      sourceCertifiedSupersingularCarrierConstructed ≡ true

    exactlyTwoSourceCertifiedClassesRepresented : Bool
    exactlyTwoSourceCertifiedClassesRepresentedIsTrue :
      exactlyTwoSourceCertifiedClassesRepresented ≡ true

    jResiduesZeroAndOneRepresented : Bool
    jResiduesZeroAndOneRepresentedIsTrue :
      jResiduesZeroAndOneRepresented ≡ true

    modularPolynomialCarrierChartConstructed : Bool
    modularPolynomialCarrierChartConstructedIsTrue :
      modularPolynomialCarrierChartConstructed ≡ true

    reducedAutomorphismOrdersConstructed : Bool
    reducedAutomorphismOrdersConstructedIsTrue :
      reducedAutomorphismOrdersConstructed ≡ true

    supersingularityDerivedFromInternalEllipticCurveArithmetic : Bool
    supersingularityDerivedFromInternalEllipticCurveArithmeticIsFalse :
      supersingularityDerivedFromInternalEllipticCurveArithmetic ≡ false

canonicalP11GeometricSupersingularBoundary : P11GeometricSupersingularBoundary
canonicalP11GeometricSupersingularBoundary =
  record
    { sourceCertifiedSupersingularCarrierConstructed = true
    ; sourceCertifiedSupersingularCarrierConstructedIsTrue = refl
    ; exactlyTwoSourceCertifiedClassesRepresented = true
    ; exactlyTwoSourceCertifiedClassesRepresentedIsTrue = refl
    ; jResiduesZeroAndOneRepresented = true
    ; jResiduesZeroAndOneRepresentedIsTrue = refl
    ; modularPolynomialCarrierChartConstructed = true
    ; modularPolynomialCarrierChartConstructedIsTrue = refl
    ; reducedAutomorphismOrdersConstructed = true
    ; reducedAutomorphismOrdersConstructedIsTrue = refl
    ; supersingularityDerivedFromInternalEllipticCurveArithmetic = false
    ; supersingularityDerivedFromInternalEllipticCurveArithmeticIsFalse = refl
    }
