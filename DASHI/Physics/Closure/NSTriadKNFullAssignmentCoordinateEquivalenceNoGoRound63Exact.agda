module DASHI.Physics.Closure.NSTriadKNFullAssignmentCoordinateEquivalenceNoGoRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Émile Picard.
-- Title: "Traité d'analyse" (successive-approximation method).
-- DOI: not applicable to the cited historical book.
--
-- Author: Ernst Lindelöf.
-- Title: "Sur l'application de la méthode des approximations successives aux
-- équations différentielles ordinaires du premier ordre".
-- DOI: not applicable to the 1894 historical article.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND 63 A/PICARD API FALSIFIER
--
-- The historical `FinitePhysicalCoordinateEquivalence` targets
--
--   Assignment = CoordinateVariable -> Q
--
-- and requires encodeDecode for EVERY coordinate variable.  Despite its name,
-- this is the full assignment function space, not an assignment restricted to
-- a finite cutoff coordinate list.
--
-- This file gives an executable no-go: the one-point physical state cannot be
-- equivalent to that assignment space because the constant-zero and
-- constant-one assignments are distinct at one explicit Fourier coordinate,
-- while every decoded physical state is the same point.
--
-- CONSEQUENCE
--
-- Round63's canonical finite Galerkin self-map should not be coerced through
-- the old full-assignment equivalence.  The Picard repair needs a genuinely
-- finite/indexed REAL coordinate carrier (or a direct finite-dimensional normed
-- carrier theorem) matched to the canonical cutoff state.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact as Coordinates

zeroAssignment : Polynomial.Assignment
zeroAssignment variable = 0ℚ

oneAssignment : Polynomial.Assignment
oneAssignment variable = 1ℚ

testVariable : Polynomial.CoordinateVariable
testVariable =
  Polynomial.coordinate-variable
    Z3.zeroMode Polynomial.xAxis Polynomial.realPart

unitUnique : (value : ⊤) → value ≡ tt
unitUnique tt = refl

zeroNotOne : ¬ (0ℚ ≡ 1ℚ)
zeroNotOne ()

unitCannotEncodeDecodeFullAssignment :
  ¬ (Coordinates.FinitePhysicalCoordinateEquivalence ⊤)
unitCannotEncodeDecodeFullAssignment equivalence =
  zeroNotOne zeroEqualsOne
  where
  decodeZeroIsDecodeOne :
    Coordinates.decode equivalence zeroAssignment
    ≡ Coordinates.decode equivalence oneAssignment
  decodeZeroIsDecodeOne =
    trans
      (unitUnique (Coordinates.decode equivalence zeroAssignment))
      (sym (unitUnique (Coordinates.decode equivalence oneAssignment)))

  encodedDecodedEqual :
    Coordinates.encode equivalence
      (Coordinates.decode equivalence zeroAssignment) testVariable
    ≡ Coordinates.encode equivalence
      (Coordinates.decode equivalence oneAssignment) testVariable
  encodedDecodedEqual =
    cong
      (λ physical → Coordinates.encode equivalence physical testVariable)
      decodeZeroIsDecodeOne

  zeroEqualsOne : 0ℚ ≡ 1ℚ
  zeroEqualsOne =
    trans
      (sym
        (Coordinates.encodeDecode equivalence zeroAssignment testVariable))
      (trans
        encodedDecodedEqual
        (Coordinates.encodeDecode equivalence oneAssignment testVariable))

oldCoordinateTargetIsFullAssignmentSpace : Bool
oldCoordinateTargetIsFullAssignmentSpace = true

canonicalPicardNeedsFiniteIndexedRealCoordinates : Bool
canonicalPicardNeedsFiniteIndexedRealCoordinates = true

oldCoordinateTargetIsFullAssignmentSpaceIsTrue :
  oldCoordinateTargetIsFullAssignmentSpace ≡ true
oldCoordinateTargetIsFullAssignmentSpaceIsTrue = refl

canonicalPicardNeedsFiniteIndexedRealCoordinatesIsTrue :
  canonicalPicardNeedsFiniteIndexedRealCoordinates ≡ true
canonicalPicardNeedsFiniteIndexedRealCoordinatesIsTrue = refl
