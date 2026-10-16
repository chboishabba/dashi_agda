module DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact where

------------------------------------------------------------------------
-- ACTUAL-HALTING CODED STANDARD POLYNOMIAL DECIDER
--
-- The earlier coded carrier padded every formula to the full polynomial budget.
-- That is stronger than P and creates an artificial self-clock obstruction.
--
-- Here runtime is an actual quiescent execution from the canonical minimal
-- standard input, with only an upper polynomial bound.  Cook guard padding is
-- represented separately by `GuardedExecutionReceipt` after the actual runtime
-- has already been fixed operationally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as InputCodec
import DASHI.Mathematics.Complexity.CodedStandardCanonicalInputExact as CanonicalInput
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as Clock
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

------------------------------------------------------------------------
-- Generic deterministic halting-time uniqueness.
------------------------------------------------------------------------

justInjective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

nothingNotJust : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothingNotJust ()

haltingExactRunLengthUnique :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {leftSteps rightSteps : Nat}
    {start leftFinish rightFinish : Standard.StandardConfiguration machine} →
  Run.StandardExactRun machine leftSteps start leftFinish →
  Standard.standardNext machine leftFinish ≡ nothing →
  Run.StandardExactRun machine rightSteps start rightFinish →
  Standard.standardNext machine rightFinish ≡ nothing →
  leftSteps ≡ rightSteps
haltingExactRunLengthUnique
    Run.standardRunDone leftHalt
    Run.standardRunDone rightHalt = refl
haltingExactRunLengthUnique
    Run.standardRunDone leftHalt
    (Run.standardRunStep rightEdge rightRest) rightHalt =
  ⊥-elim (nothingNotJust (trans (sym leftHalt) rightEdge))
haltingExactRunLengthUnique
    (Run.standardRunStep leftEdge leftRest) leftHalt
    Run.standardRunDone rightHalt =
  ⊥-elim (nothingNotJust (trans (sym rightHalt) leftEdge))
haltingExactRunLengthUnique
    (Run.standardRunStep leftEdge leftRest) leftHalt
    (Run.standardRunStep rightEdge rightRest) rightHalt
  with justInjective (trans (sym leftEdge) rightEdge)
... | refl =
  congSuc
    (haltingExactRunLengthUnique
      leftRest leftHalt rightRest rightHalt)
  where
    congSuc : ∀ {m n : Nat} → m ≡ n → suc m ≡ suc n
    congSuc refl = refl

------------------------------------------------------------------------
-- Machine-bearing polynomial-time decider using actual halting runtime.
------------------------------------------------------------------------

record CodedStandardHaltingPolynomialDecider
    (decider : Cook.BooleanFormula → Bool) : Set where
  field
    code : Coded.CodedFiniteStandardTM

    zeroSymbol : Data.Fin.Base.Fin (Coded.symbolCount code)
    oneSymbol : Data.Fin.Base.Fin (Coded.symbolCount code)
    binarySymbolsDistinct : zeroSymbol ≡ oneSymbol → ⊥
    zeroSymbolNotBlank : zeroSymbol ≡ Coded.blank code → ⊥
    oneSymbolNotBlank : oneSymbol ≡ Coded.blank code → ⊥

    clockCoefficient : Nat
    clockDegree : Nat

    actualSteps : Cook.BooleanFormula → Nat

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
        (actualSteps formula)
        (CanonicalInput.canonicalStandardStart
          (InputCodec.formulaInput code zeroSymbol oneSymbol formula))
        (finish formula)

    finishQuiescent :
      (formula : Cook.BooleanFormula) →
      Standard.standardNext
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM code))
        (finish formula)
      ≡ nothing

    actualStepsPolynomialBound :
      (formula : Cook.BooleanFormula) →
      actualSteps formula
      ≤ Clock.formulaPolynomialBudget
          clockCoefficient clockDegree formula

    decisionExact :
      (formula : Cook.BooleanFormula) →
      Coded.finEqual
        (Standard.state (finish formula))
        (Coded.acceptingState code)
      ≡ decider formula

open CodedStandardHaltingPolynomialDecider public

actualStepsOperationallyUnique :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : CodedStandardHaltingPolynomialDecider decider)
    (formula : Cook.BooleanFormula)
    (otherSteps : Nat)
    (otherFinish : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (code witness)))) →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (code witness)))
    otherSteps
    (CanonicalInput.canonicalStandardStart
      (InputCodec.formulaInput
        (code witness)
        (zeroSymbol witness)
        (oneSymbol witness)
        formula))
    otherFinish →
  Standard.standardNext
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (code witness)))
    otherFinish
  ≡ nothing →
  actualSteps witness formula ≡ otherSteps
actualStepsOperationallyUnique witness formula otherSteps otherFinish otherRun otherHalt =
  haltingExactRunLengthUnique
    (execution witness formula)
    (finishQuiescent witness formula)
    otherRun
    otherHalt

------------------------------------------------------------------------
-- Downstream Cook padding transport.
--
-- This receipt does not choose the runtime.  It must realize the already-fixed
-- `actualSteps` from the guarded representation used by Cook--Levin.
------------------------------------------------------------------------

record GuardedExecutionReceipt
    {decider : Cook.BooleanFormula → Bool}
    (witness : CodedStandardHaltingPolynomialDecider decider) : Set where
  field
    guardedFinish :
      (formula : Cook.BooleanFormula) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM (code witness)))

    guardedExecution :
      (formula : Cook.BooleanFormula) →
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM (code witness)))
        (actualSteps witness formula)
        (Language.guardedStandardStart
          (InputCodec.formulaInput
            (code witness)
            (zeroSymbol witness)
            (oneSymbol witness)
            formula)
          (actualSteps witness formula))
        (guardedFinish formula)

    guardedDecisionExact :
      (formula : Cook.BooleanFormula) →
      Coded.finEqual
        (Standard.state (guardedFinish formula))
        (Coded.acceptingState (code witness))
      ≡ decider formula

open GuardedExecutionReceipt public

------------------------------------------------------------------------
-- BOUNDARY
--
-- * actualSteps is tied to a unique quiescent run from one canonical input;
-- * only an upper polynomial bound is required;
-- * guarded padding is downstream and cannot select a different runtime;
-- * deriving GuardedExecutionReceipt generically is now an explicit ordinary
--   blank-padding/model-transport theorem rather than a timing oracle.
------------------------------------------------------------------------
