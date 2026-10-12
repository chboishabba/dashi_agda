module DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact where

------------------------------------------------------------------------
-- SET-LEVEL CODED POLYNOMIAL DECIDER WITNESS
--
-- CodedFiniteStandardMachineExact pays a low-universe finite program carrier.
-- Here we add the SAT-facing data that can genuinely inhabit a
-- `polynomialTimeDecider : (Word -> Bool) -> Set` predicate:
--
--   * one coded finite deterministic standard TM;
--   * two literal tape symbols used for the canonical BooleanFormula bit code;
--   * exact T-step standard execution on that canonical input;
--   * final-control decision equality;
--   * explicit arithmetic polynomial bound on T.
--
-- All state/symbol carriers are `Fin n`, so this witness itself lives in Set.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size

------------------------------------------------------------------------
-- Canonical formula bits -> the coded machine's chosen binary tape symbols.
------------------------------------------------------------------------

mapFormulaBits :
  ∀ {n : Nat} →
  Fin.Fin n →
  Fin.Fin n →
  List Bool →
  List (Fin.Fin n)
mapFormulaBits zeroSymbol oneSymbol [] = []
mapFormulaBits zeroSymbol oneSymbol (false ∷ bits) =
  zeroSymbol ∷ mapFormulaBits zeroSymbol oneSymbol bits
mapFormulaBits zeroSymbol oneSymbol (true ∷ bits) =
  oneSymbol ∷ mapFormulaBits zeroSymbol oneSymbol bits

formulaInput :
  (code : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.symbolCount code) →
  Fin.Fin (Coded.symbolCount code) →
  Cook.BooleanFormula →
  List (Fin.Fin (Coded.symbolCount code))
formulaInput code zeroSymbol oneSymbol formula =
  mapFormulaBits zeroSymbol oneSymbol
    (Binary.encodeFormulaBits formula)

------------------------------------------------------------------------
-- Ordinary arithmetic polynomial clock shape.
------------------------------------------------------------------------

natPower : Nat → Nat → Nat
natPower base zero = suc zero
natPower base (suc exponent) = base * natPower base exponent

polynomialStepBudget :
  Nat → Nat → Cook.BooleanFormula → Nat
polynomialStepBudget coefficient degree formula =
  coefficient * natPower (suc (Size.formulaNodeCount formula)) degree

------------------------------------------------------------------------
-- Genuine Set-level machine-bearing decider witness.
------------------------------------------------------------------------

record CodedStandardPolynomialDecider
    (decider : Cook.BooleanFormula → Bool) : Set where
  field
    code : Coded.CodedFiniteStandardTM

    zeroSymbol : Fin.Fin (Coded.symbolCount code)
    oneSymbol : Fin.Fin (Coded.symbolCount code)

    clockCoefficient : Nat
    clockDegree : Nat
    exactSteps : Cook.BooleanFormula → Nat

    finish :
      (formula : Cook.BooleanFormula) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM code))

    execution :
      (formula : Cook.BooleanFormula) →
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM code))
        (exactSteps formula)
        (Language.guardedStandardStart
          (formulaInput code zeroSymbol oneSymbol formula)
          (exactSteps formula))
        (finish formula)

    decisionExact :
      (formula : Cook.BooleanFormula) →
      Coded.finEqual
        (Standard.state (finish formula))
        (Coded.acceptingState code)
      ≡ decider formula

    exactStepsPolynomialBound :
      (formula : Cook.BooleanFormula) →
      exactSteps formula
      ≤ polynomialStepBudget clockCoefficient clockDegree formula

open CodedStandardPolynomialDecider public

------------------------------------------------------------------------
-- Boundary/status.
------------------------------------------------------------------------

record CodedStandardPolynomialDeciderBoundary : Set where
  constructor coded-standard-polynomial-decider-boundary
  field
    finiteProgramCodeInSet : Bool
    canonicalFormulaBitInput : Bool
    exactStandardRunCarried : Bool
    finalDecisionExact : Bool
    arithmeticPolynomialClockCarried : Bool
    mapPrecompositionClosurePaid : Bool
    verifierClosurePaid : Bool

canonicalCodedStandardPolynomialDeciderBoundary :
  CodedStandardPolynomialDeciderBoundary
canonicalCodedStandardPolynomialDeciderBoundary =
  coded-standard-polynomial-decider-boundary
    true true true true true false false

------------------------------------------------------------------------
-- FRONTIER
--
-- The decider representation part of a concrete standard-machine cost model is
-- now a literal Set-level predicate. A future PolynomialCostModel can set
-- `polynomialTimeDecider = CodedStandardPolynomialDecider` without any
-- extensional-code extraction theorem.
--
-- The remaining cost-model engineering is closure, not representation:
-- provide equally coded polynomial maps/verifiers and compile precomposition.
------------------------------------------------------------------------
