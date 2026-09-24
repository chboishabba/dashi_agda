module DASHI.Mathematics.Complexity.PNotEqualsNPCircuitCarrierNoGoExact where

------------------------------------------------------------------------
-- EXISTING BOOLEAN-CIRCUIT CARRIER IS TOO WEAK FOR P/poly NORMALIZATION
--
-- CookLevinCircuitGCTBoundary.BooleanCircuitFamily intentionally records only a
-- broad boundary:
--
--   Circuit : Set
--   evaluateCircuit : Circuit -> Input -> Bool
--   circuitForSize : Nat -> Circuit
--   circuitSize : Circuit -> Nat
--   polynomialSizeBound : Set
--   computesLanguage : Input -> Set
--   circuitCorrect : Set
--
-- The last two fields are not yet tied by a theorem to evaluateCircuit, and the
-- Circuit carrier is arbitrary.  Therefore this record can be instantiated by
-- an extensional Boolean function itself and assigned zero "circuit size".
--
-- Conclusion: the existing carrier cannot be used as the P/poly normalization
-- target for the Clay-critical self-diagonal lane without a stronger concrete
-- gate/encoding semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Unit using (⊤; tt)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct

------------------------------------------------------------------------
-- Any Boolean consumer yields a zero-size inhabitant of the current abstract
-- circuit-family carrier.
------------------------------------------------------------------------

zeroSizeExtensionalCircuitFamily :
  ∀ {Input : Set} →
  (consumer : Input → Bool) →
  Cook.BooleanCircuitFamily
zeroSizeExtensionalCircuitFamily {Input} consumer = record
  { Cook.Input = Input
  ; Cook.Circuit = Input → Bool
  ; Cook.evaluateCircuit =
      λ circuit input → circuit input
  ; Cook.circuitForSize =
      λ size → consumer
  ; Cook.circuitSize =
      λ circuit → zero
  ; Cook.inputLength =
      λ input → zero
  ; Cook.polynomialSizeBound =
      ⊤
  ; Cook.computesLanguage =
      λ input → ⊤
  ; Cook.circuitCorrect =
      ⊤
  }

zeroSizeExtensionalCircuitFamilyHasDeclaredBound :
  ∀ {Input : Set}
    (consumer : Input → Bool) →
  Cook.polynomialSizeBound
    (zeroSizeExtensionalCircuitFamily consumer)
zeroSizeExtensionalCircuitFamilyHasDeclaredBound consumer =
  tt

zeroSizeExtensionalCircuitFamilyHasDeclaredCorrectness :
  ∀ {Input : Set}
    (consumer : Input → Bool) →
  Cook.circuitCorrect
    (zeroSizeExtensionalCircuitFamily consumer)
zeroSizeExtensionalCircuitFamilyHasDeclaredCorrectness consumer =
  tt

------------------------------------------------------------------------
-- SAT-candidate specialization.
------------------------------------------------------------------------

candidateHasZeroSizeAbstractCircuitFamily :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Direct.PolynomialSATDeciderCandidate cost →
  Cook.BooleanCircuitFamily
candidateHasZeroSizeAbstractCircuitFamily candidate =
  zeroSizeExtensionalCircuitFamily
    (Direct.decide candidate)

candidateAbstractCircuitEvaluatesExactly :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (size : Nat)
    (formula : Cook.BooleanFormula) →
  Cook.evaluateCircuit
      (candidateHasZeroSizeAbstractCircuitFamily candidate)
      (Cook.circuitForSize
        (candidateHasZeroSizeAbstractCircuitFamily candidate)
        size)
      formula
  ≡ Direct.decide candidate formula
candidateAbstractCircuitEvaluatesExactly candidate size formula =
  refl

candidateAbstractCircuitSizeIsZero :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (size : Nat) →
  Cook.circuitSize
      (candidateHasZeroSizeAbstractCircuitFamily candidate)
      (Cook.circuitForSize
        (candidateHasZeroSizeAbstractCircuitFamily candidate)
        size)
  ≡ zero
candidateAbstractCircuitSizeIsZero candidate size =
  refl

------------------------------------------------------------------------
-- Consequence.
--
-- Any circuit lower-bound argument intended to imply SAT notin P must target a
-- stronger carrier whose gate syntax, input encoding, gate count and semantic
-- correctness are linked by actual theorems.  The current boundary record is
-- useful organizationally but cannot support a Clay-critical P/poly lower
-- bound.
------------------------------------------------------------------------
