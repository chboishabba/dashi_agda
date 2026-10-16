module DASHI.Mathematics.Complexity.CodedStandardGuardedExecutionCompilerExact where

------------------------------------------------------------------------
-- ACTUAL-HALTING STANDARD RUN -> GUARDED COOK REPRESENTATION
--
-- Runtime starts on the conventional split tape with implicit blank tails.
-- `GuardedStandardStartBlankTailExact` proves that the Cook guarded start is the
-- same infinite tape with a finite blank margin materialised explicitly.
-- `StandardBlankTailBisimulationExact` transports the already-fixed actual run
-- to that representation without changing the number of machine steps or the
-- final control state.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardBlankTailBisimulationExact as BlankTail
import DASHI.Mathematics.Complexity.GuardedStandardStartBlankTailExact as Start
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as InputCodec
import DASHI.Mathematics.Complexity.CodedStandardCanonicalInputExact as CanonicalInput
import DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact as Halting

------------------------------------------------------------------------
-- Every actual-halting candidate gets its guarded Cook execution mechanically.
------------------------------------------------------------------------

guardedExecutionReceiptOfHaltingWitness :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider) →
  Halting.GuardedExecutionReceipt witness
guardedExecutionReceiptOfHaltingWitness witness = record
  { Halting.guardedFinish = guardedFinish
  ; Halting.guardedExecution = guardedExecution
  ; Halting.guardedDecisionExact = guardedDecisionExact
  }
  where
    machine : Standard.StandardSingleTapeMachine
      (Fin.Fin (Coded.stateCount (Halting.code witness)))
      (Fin.Fin (Coded.symbolCount (Halting.code witness)))
    machine =
      Presented.finitePresentedStandardMachine
        (Coded.decodeCodedStandardTM (Halting.code witness))

    input : Cook.BooleanFormula →
      Input.InputWord
        (Presented.finitePresentedStandardToConcrete
          (Coded.decodeCodedStandardTM (Halting.code witness)))
    input formula =
      InputCodec.formulaInput
        (Halting.code witness)
        (Halting.zeroSymbol witness)
        (Halting.oneSymbol witness)
        formula

    startEq :
      (formula : Cook.BooleanFormula) →
      BlankTail.ConfigurationBlankTailEq
        (CanonicalInput.canonicalStandardStart (input formula))
        (Language.guardedStandardStart
          (input formula)
          (Halting.actualSteps witness formula))
    startEq formula =
      Start.guardedStandardStartBlankTailEq
        (input formula)
        (Halting.actualSteps witness formula)

    transported :
      (formula : Cook.BooleanFormula) →
      Σ (Standard.StandardConfiguration machine) λ finish →
        Run.StandardExactRun
          machine
          (Halting.actualSteps witness formula)
          (Language.guardedStandardStart
            (input formula)
            (Halting.actualSteps witness formula))
          finish
        × BlankTail.ConfigurationBlankTailEq
            (Halting.finish witness formula)
            finish
    transported formula =
      BlankTail.transportExactRunAcrossBlankTailEq
        (startEq formula)
        (Halting.execution witness formula)

    guardedFinish :
      (formula : Cook.BooleanFormula) →
      Standard.StandardConfiguration machine
    guardedFinish formula = proj₁ (transported formula)

    guardedExecution :
      (formula : Cook.BooleanFormula) →
      Run.StandardExactRun
        machine
        (Halting.actualSteps witness formula)
        (Language.guardedStandardStart
          (input formula)
          (Halting.actualSteps witness formula))
        (guardedFinish formula)
    guardedExecution formula = proj₁ (proj₂ (transported formula))

    finishEq :
      (formula : Cook.BooleanFormula) →
      BlankTail.ConfigurationBlankTailEq
        (Halting.finish witness formula)
        (guardedFinish formula)
    finishEq formula = proj₂ (proj₂ (transported formula))

    guardedDecisionExact :
      (formula : Cook.BooleanFormula) →
      Coded.finEqual
        (Standard.state (guardedFinish formula))
        (Coded.acceptingState (Halting.code witness))
      ≡ decider formula
    guardedDecisionExact formula =
      trans
        (sym
          (cong
            (λ q → Coded.finEqual q (Coded.acceptingState (Halting.code witness)))
            (BlankTail.stateEq (finishEq formula))))
        (Halting.decisionExact witness formula)

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record GuardedExecutionCompilerBoundary : Set where
  constructor guarded-execution-compiler-boundary
  field
    canonicalInputIndependentOfCookPadding : Bool
    guardedStartSameInfiniteTapePaid : Bool
    exactRunLengthTransportPaid : Bool
    guardedDecisionPreserved : Bool
    guardedExecutionReceiptConstructed : Bool
    cookPaddingChoosesRuntime : Bool

canonicalGuardedExecutionCompilerBoundary : GuardedExecutionCompilerBoundary
canonicalGuardedExecutionCompilerBoundary =
  guarded-execution-compiler-boundary
    true true true true true false

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- `GuardedExecutionReceipt` is now a representation compiler, not a mathematical
-- premise: materialising finite blank tails for Cook--Levin preserves the same
-- operational run, step count and decision.  The remaining Clay-critical work is
-- therefore the candidate-aware behavioural self-specializer and the final
-- program-size/runtime/Cook resource fixed point.
------------------------------------------------------------------------
