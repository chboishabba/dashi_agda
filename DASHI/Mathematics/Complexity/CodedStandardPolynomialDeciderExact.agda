module DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact where

------------------------------------------------------------------------
-- SET-LEVEL CODED POLYNOMIAL DECIDER WITNESS
--
-- IMPORTANT RESOURCE FIREWALL
--
-- The execution clock is NOT an arbitrary Formula -> Nat field.  The guarded
-- finite simulation itself depends on T, so such a field could become an input
-- side-channel.  The concrete model instead runs for the canonical size-only
-- arithmetic clock
--
--   T(phi) = c * (1 + |phi|)^d.
--
-- Likewise the two symbols used by the binary formula input are required to be
-- distinct; otherwise the serialized formula could collapse before execution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as ClockArithmetic

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

polynomialStepBudget :
  Nat → Nat → Cook.BooleanFormula → Nat
polynomialStepBudget = ClockArithmetic.formulaPolynomialBudget

record CodedStandardPolynomialDecider
    (decider : Cook.BooleanFormula → Bool) : Set where
  field
    code : Coded.CodedFiniteStandardTM

    zeroSymbol : Fin.Fin (Coded.symbolCount code)
    oneSymbol : Fin.Fin (Coded.symbolCount code)
    binarySymbolsDistinct : zeroSymbol ≡ oneSymbol → ⊥

    clockCoefficient : Nat
    clockDegree : Nat

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
        (polynomialStepBudget clockCoefficient clockDegree formula)
        (Language.guardedStandardStart
          (formulaInput code zeroSymbol oneSymbol formula)
          (polynomialStepBudget clockCoefficient clockDegree formula))
        (finish formula)

    decisionExact :
      (formula : Cook.BooleanFormula) →
      Coded.finEqual
        (Standard.state (finish formula))
        (Coded.acceptingState code)
      ≡ decider formula

open CodedStandardPolynomialDecider public

record CodedStandardPolynomialDeciderBoundary : Set where
  constructor coded-standard-polynomial-decider-boundary
  field
    finiteProgramCodeInSet : Bool
    faithfulBinaryInputSymbols : Bool
    canonicalSizeOnlyPolynomialClock : Bool
    exactStandardRunCarried : Bool
    finalDecisionExact : Bool
    arbitraryFormulaDependentClockAllowed : Bool
    mapPrecompositionClosurePaid : Bool
    verifierClosurePaid : Bool

canonicalCodedStandardPolynomialDeciderBoundary :
  CodedStandardPolynomialDeciderBoundary
canonicalCodedStandardPolynomialDeciderBoundary =
  coded-standard-polynomial-decider-boundary
    true true true true true false false false

------------------------------------------------------------------------
-- FRONTIER
--
-- `polynomialTimeDecider = CodedStandardPolynomialDecider` is now a genuine
-- machine-bearing Set-level predicate with a faithful canonical bit input and
-- a size-only polynomial clock.  No hidden extensional timing oracle remains.
------------------------------------------------------------------------
