module DASHI.Mathematics.Complexity.PNotEqualsNPExtensionalQuotationNoGoExact where

------------------------------------------------------------------------
-- EXTENSIONAL FUNCTION QUOTATION NO-GO
--
-- Resource-bounded self-reference needs a finite description of the candidate
-- SAT decider.  The current PolynomialSATDeciderCandidate stores only an
-- extensional function BooleanFormula -> Bool plus a polynomial-time predicate.
--
-- This file proves a constructive Cantor-style fact:
--
--   there is no Nat-indexed enumeration/quotation of ALL
--   BooleanFormula -> Bool functions.
--
-- This does NOT show polynomial-time deciders are uncountable; they are
-- expected to be machine-describable.  It shows only that quotation cannot be
-- recovered from the bare Agda function type.  A self-diagonal construction
-- must therefore consume an explicit program/machine presentation.
--
-- Source calibration:
--   Georg Cantor,
--   "Über eine elementare Frage der Mannigfaltigkeitslehre",
--   Jahresbericht der Deutschen Mathematiker-Vereinigung 1 (1891), 75--78.
--   No DOI is asserted in the repository source atlas.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPDiagonalizationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- Pointwise equality and Boolean diagonal contradiction.
------------------------------------------------------------------------

PointwiseEqual :
  ∀ {A B : Set} →
  (A → B) →
  (A → B) →
  Set
PointwiseEqual left right =
  ∀ input → left input ≡ right input

boolCannotEqualItsNegation :
  (value : Bool) →
  value ≡ Cook.notBool value →
  ⊥
boolCannotEqualItsNegation true ()
boolCannotEqualItsNegation false ()

------------------------------------------------------------------------
-- Warm-up: Nat -> Bool sequences are not Nat-enumerable.
------------------------------------------------------------------------

diagonalBooleanSequence :
  (decode : Nat → Nat → Bool) →
  Nat →
  Bool
diagonalBooleanSequence decode index =
  Cook.notBool (decode index index)

NoNatEnumerationOfBooleanSequences :
  Set₁
NoNatEnumerationOfBooleanSequences =
  (decode : Nat → Nat → Bool) →
  ((sequence : Nat → Bool) →
    Σ Nat (λ code →
      PointwiseEqual (decode code) sequence)) →
  ⊥

noNatEnumerationOfBooleanSequences :
  NoNatEnumerationOfBooleanSequences
noNatEnumerationOfBooleanSequences decode allegedlySurjective
    with allegedlySurjective (diagonalBooleanSequence decode)
... | code , decodedEqualsDiagonal =
  boolCannotEqualItsNegation
    (decode code code)
    (decodedEqualsDiagonal code)

------------------------------------------------------------------------
-- Direct specialization to SAT-formula consumers.
------------------------------------------------------------------------

diagonalFormulaConsumer :
  (decode : Nat → Cook.BooleanFormula → Bool) →
  Cook.BooleanFormula →
  Bool
diagonalFormulaConsumer decode (Cook.variable index) =
  Cook.notBool (decode index (Cook.variable index))
diagonalFormulaConsumer decode (Cook.constant value) =
  false
diagonalFormulaConsumer decode (Cook.negate formula) =
  false
diagonalFormulaConsumer decode (Cook.conjunction left right) =
  false
diagonalFormulaConsumer decode (Cook.disjunction left right) =
  false

NoNatQuotationOfAllFormulaConsumers :
  Set₁
NoNatQuotationOfAllFormulaConsumers =
  (decode : Nat → Cook.BooleanFormula → Bool) →
  ((consumer : Cook.BooleanFormula → Bool) →
    Σ Nat (λ code →
      PointwiseEqual (decode code) consumer)) →
  ⊥

noNatQuotationOfAllFormulaConsumers :
  NoNatQuotationOfAllFormulaConsumers
noNatQuotationOfAllFormulaConsumers decode allegedlySurjective
    with allegedlySurjective (diagonalFormulaConsumer decode)
... | code , decodedEqualsDiagonal =
  boolCannotEqualItsNegation
    (decode code (Cook.variable code))
    (decodedEqualsDiagonal (Cook.variable code))

------------------------------------------------------------------------
-- Consequence for the P != NP self-reference lane.
--
-- The theorem above is intentionally NOT a lower bound on polynomial-time
-- functions.  It proves that an arbitrary extensional function value is not
-- automatically a finite program description.  Any resource-bounded diagonal
-- theorem must introduce a separate machine/program code carrier and prove
-- that the polynomial SAT candidate under attack is represented by that code.
------------------------------------------------------------------------
