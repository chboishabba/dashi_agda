module DASHI.Physics.Closure.NSTriadKNFiniteGalerkinVectorLipschitzRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Round 28 proved the local-Lipschitz estimate for one literal Galerkin
-- coordinate. This file lifts that theorem to the complete finite coordinate
-- list. The output norm is the literal l1 sum of coordinate differences, and
-- its Lipschitz constant is the exact sum of the coordinate atom weights.
-- No generic polynomial receipt is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinLocalLipschitzRound28Exact as Coordinate

finiteVectorDifferenceL1 :
  List Polynomial.LiteralGalerkinCoordinateEquation →
  Polynomial.Assignment → Polynomial.Assignment → ℚ
finiteVectorDifferenceL1 [] state reference = 0ℚ
finiteVectorDifferenceL1 (equation ∷ rest) state reference =
  ∣ Polynomial.coordinateRightHandSide equation state
    - Polynomial.coordinateRightHandSide equation reference ∣
  + finiteVectorDifferenceL1 rest state reference

finiteVectorLipschitzWeight :
  ℚ → List Polynomial.LiteralGalerkinCoordinateEquation → ℚ
finiteVectorLipschitzWeight radius [] = 0ℚ
finiteVectorLipschitzWeight radius (equation ∷ rest) =
  Coordinate.atomsLipschitzWeight radius
    (Polynomial.rightHandSideAtoms equation)
  + finiteVectorLipschitzWeight radius rest

finiteGalerkinVectorLocalLipschitz :
  (radius delta : ℚ) →
  0ℚ ≤ radius →
  0ℚ ≤ delta →
  (equations : List Polynomial.LiteralGalerkinCoordinateEquation) →
  (state reference : Polynomial.Assignment) →
  Coordinate.AssignmentBound radius state →
  Coordinate.AssignmentBound radius reference →
  Coordinate.AssignmentDifferenceBound delta state reference →
  finiteVectorDifferenceL1 equations state reference
  ≤ finiteVectorLipschitzWeight radius equations * delta
finiteGalerkinVectorLocalLipschitz
  radius delta radiusNN deltaNN []
  state reference stateBound referenceBound differenceBound =
  subst
    (λ upper → 0ℚ ≤ upper)
    (solve (delta ∷ []))
    ℚₚ.≤-refl
finiteGalerkinVectorLocalLipschitz
  radius delta radiusNN deltaNN (equation ∷ rest)
  state reference stateBound referenceBound differenceBound =
  let
    coordinateBound =
      Coordinate.coordinateRightHandSideLocalLipschitz
        radius delta radiusNN deltaNN equation state reference
        stateBound referenceBound differenceBound

    restBound =
      finiteGalerkinVectorLocalLipschitz
        radius delta radiusNN deltaNN rest state reference
        stateBound referenceBound differenceBound

    summed = ℚₚ.+-mono-≤ coordinateBound restBound

    rightMeaning :
      Coordinate.atomsLipschitzWeight radius
        (Polynomial.rightHandSideAtoms equation) * delta
      + finiteVectorLipschitzWeight radius rest * delta
      ≡ finiteVectorLipschitzWeight radius (equation ∷ rest) * delta
    rightMeaning =
      solve
        ( Coordinate.atomsLipschitzWeight radius
            (Polynomial.rightHandSideAtoms equation)
        ∷ finiteVectorLipschitzWeight radius rest
        ∷ delta
        ∷ [])
  in
  subst
    (λ upper →
      finiteVectorDifferenceL1 (equation ∷ rest) state reference
      ≤ upper)
    rightMeaning
    summed

record LiteralFiniteGalerkinVectorField : Set where
  constructor literal-finite-galerkin-vector-field
  field
    coordinateEquations :
      List Polynomial.LiteralGalerkinCoordinateEquation

open LiteralFiniteGalerkinVectorField public

literalFiniteVectorFieldLocalLipschitz :
  (field : LiteralFiniteGalerkinVectorField) →
  (radius delta : ℚ) →
  0ℚ ≤ radius →
  0ℚ ≤ delta →
  (state reference : Polynomial.Assignment) →
  Coordinate.AssignmentBound radius state →
  Coordinate.AssignmentBound radius reference →
  Coordinate.AssignmentDifferenceBound delta state reference →
  finiteVectorDifferenceL1
    (coordinateEquations field) state reference
  ≤ finiteVectorLipschitzWeight
      radius (coordinateEquations field) * delta
literalFiniteVectorFieldLocalLipschitz
  field radius delta radiusNN deltaNN state reference
  stateBound referenceBound differenceBound =
  finiteGalerkinVectorLocalLipschitz
    radius delta radiusNN deltaNN
    (coordinateEquations field)
    state reference stateBound referenceBound differenceBound

finiteRationalVectorLocalLipschitzClosed : Bool
finiteRationalVectorLocalLipschitzClosed = true

continuumRealCoordinateEquivalenceClosed : Bool
continuumRealCoordinateEquivalenceClosed = false

finiteRationalVectorLocalLipschitzClosedIsTrue :
  finiteRationalVectorLocalLipschitzClosed ≡ true
finiteRationalVectorLocalLipschitzClosedIsTrue = refl

continuumRealCoordinateEquivalenceClosedIsFalse :
  continuumRealCoordinateEquivalenceClosed ≡ false
continuumRealCoordinateEquivalenceClosedIsFalse = refl
