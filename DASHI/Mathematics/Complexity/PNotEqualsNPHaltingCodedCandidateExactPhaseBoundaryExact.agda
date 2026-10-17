module DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCodedCandidateExactPhaseBoundaryExact where

------------------------------------------------------------------------
-- ACTUAL-HALTING CODED CANDIDATE -> QUIESCENT EXACT-RUNTIME PHASE BOUNDARY
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as InputCodec
import DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact as Halting
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseRunExact as PhaseRun
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

candidatePhaseCode :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider) →
  Cook.BooleanFormula → Coded.CodedFiniteStandardTM
candidatePhaseCode witness formula =
  Phase.phaseLiftCode
    (Halting.code witness)
    (Halting.actualSteps witness formula)

candidatePhaseStart :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Standard.StandardConfiguration
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (candidatePhaseCode witness formula)))
candidatePhaseStart witness formula =
  PhaseRun.phaseEmbedAt
    (Halting.code witness)
    Fin.zero
    (Language.guardedStandardStart
      (InputCodec.formulaInput
        (Halting.code witness)
        (Halting.zeroSymbol witness)
        (Halting.oneSymbol witness)
        formula)
      (Halting.actualSteps witness formula))

candidatePhaseFinish :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider)
    (guarded : Halting.GuardedExecutionReceipt witness)
    (formula : Cook.BooleanFormula) →
  Standard.StandardConfiguration
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (candidatePhaseCode witness formula)))
candidatePhaseFinish witness guarded formula =
  PhaseRun.phaseEmbedAt
    (Halting.code witness)
    (Phase.lastPhase (Halting.actualSteps witness formula))
    (Halting.guardedFinish guarded formula)

candidatePhaseExecution :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider)
    (guarded : Halting.GuardedExecutionReceipt witness)
    (formula : Cook.BooleanFormula) →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (candidatePhaseCode witness formula)))
    (Halting.actualSteps witness formula)
    (candidatePhaseStart witness formula)
    (candidatePhaseFinish witness guarded formula)
candidatePhaseExecution witness guarded formula =
  PhaseRun.phaseLiftExactRun (Halting.guardedExecution guarded formula)

phaseAcceptingImpliesSourceAccepting :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider)
    (guarded : Halting.GuardedExecutionReceipt witness)
    (formula : Cook.BooleanFormula) →
  Standard.state (candidatePhaseFinish witness guarded formula)
    ≡ Coded.acceptingState (candidatePhaseCode witness formula) →
  Standard.state (Halting.guardedFinish guarded formula)
    ≡ Coded.acceptingState (Halting.code witness)
phaseAcceptingImpliesSourceAccepting witness guarded formula equality =
  Phase.combineFirstInjective equality

sourceAcceptingImpliesPhaseAccepting :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider)
    (guarded : Halting.GuardedExecutionReceipt witness)
    (formula : Cook.BooleanFormula) →
  Standard.state (Halting.guardedFinish guarded formula)
    ≡ Coded.acceptingState (Halting.code witness) →
  Standard.state (candidatePhaseFinish witness guarded formula)
    ≡ Coded.acceptingState (candidatePhaseCode witness formula)
sourceAcceptingImpliesPhaseAccepting witness guarded formula sourceAccepting =
  cong
    (Phase.phaseTerminalState
      (Halting.code witness)
      (Halting.actualSteps witness formula))
    sourceAccepting

candidatePhaseAcceptanceIff :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider)
    (guarded : Halting.GuardedExecutionReceipt witness)
    (formula : Cook.BooleanFormula) →
  (Standard.state (candidatePhaseFinish witness guarded formula)
      ≡ Coded.acceptingState (candidatePhaseCode witness formula)
   → Standard.state (Halting.guardedFinish guarded formula)
      ≡ Coded.acceptingState (Halting.code witness))
  ×
  (Standard.state (Halting.guardedFinish guarded formula)
      ≡ Coded.acceptingState (Halting.code witness)
   → Standard.state (candidatePhaseFinish witness guarded formula)
      ≡ Coded.acceptingState (candidatePhaseCode witness formula))
candidatePhaseAcceptanceIff witness guarded formula =
  phaseAcceptingImpliesSourceAccepting witness guarded formula ,
  sourceAcceptingImpliesPhaseAccepting witness guarded formula

candidatePhaseEndpointTransitionNothing :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider)
    (guarded : Halting.GuardedExecutionReceipt witness)
    (formula : Cook.BooleanFormula) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (candidatePhaseCode witness formula)))
    (Standard.state (candidatePhaseFinish witness guarded formula))
    (Standard.scanned (candidatePhaseFinish witness guarded formula))
  ≡ nothing
candidatePhaseEndpointTransitionNothing witness guarded formula =
  Phase.terminalStandardTransitionNothing
    (Halting.code witness)
    (Halting.actualSteps witness formula)
    (Standard.state (Halting.guardedFinish guarded formula))
    (Standard.scanned (Halting.guardedFinish guarded formula))

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Exact return freshness is indexed by the machine's actual operational
-- halting runtime, not by its polynomial upper bound.
------------------------------------------------------------------------
