module DASHI.Mathematics.Complexity.PNotEqualsNPCodedCandidateExactPhaseBoundaryExact where

------------------------------------------------------------------------
-- CODED POLYNOMIAL CANDIDATE -> EXACT QUIESCENT T-BOUNDARY
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (nothing)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as Decider
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseRunExact as PhaseRun
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

candidateSteps :
  ∀ {decider : Cook.BooleanFormula → Bool} →
  Decider.CodedStandardPolynomialDecider decider →
  Cook.BooleanFormula → Nat
candidateSteps witness formula =
  Decider.polynomialStepBudget
    (Decider.clockCoefficient witness)
    (Decider.clockDegree witness)
    formula

candidatePhaseCode :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider) →
  Cook.BooleanFormula →
  Coded.CodedFiniteStandardTM
candidatePhaseCode witness formula =
  Phase.phaseLiftCode
    (Decider.code witness)
    (candidateSteps witness formula)

candidatePhaseStart :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Standard.StandardConfiguration
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (candidatePhaseCode witness formula)))
candidatePhaseStart witness formula =
  PhaseRun.phaseEmbedAt
    (Decider.code witness)
    Fin.zero
    (Language.guardedStandardStart
      (Decider.formulaInput
        (Decider.code witness)
        (Decider.zeroSymbol witness)
        (Decider.oneSymbol witness)
        formula)
      (candidateSteps witness formula))

candidatePhaseFinish :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Standard.StandardConfiguration
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (candidatePhaseCode witness formula)))
candidatePhaseFinish witness formula =
  PhaseRun.phaseEmbedAt
    (Decider.code witness)
    (Phase.lastPhase (candidateSteps witness formula))
    (Decider.finish witness formula)

candidatePhaseExecution :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Run.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (candidatePhaseCode witness formula)))
    (candidateSteps witness formula)
    (candidatePhaseStart witness formula)
    (candidatePhaseFinish witness formula)
candidatePhaseExecution witness formula =
  PhaseRun.phaseLiftExactRun
    (Decider.execution witness formula)

candidatePhaseFinishStateExact :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Standard.state (candidatePhaseFinish witness formula)
  ≡
  Phase.phaseTerminalState
    (Decider.code witness)
    (candidateSteps witness formula)
    (Standard.state (Decider.finish witness formula))
candidatePhaseFinishStateExact witness formula = refl

phaseAcceptingImpliesSourceAccepting :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Standard.state (candidatePhaseFinish witness formula)
    ≡ Coded.acceptingState (candidatePhaseCode witness formula) →
  Standard.state (Decider.finish witness formula)
    ≡ Coded.acceptingState (Decider.code witness)
phaseAcceptingImpliesSourceAccepting witness formula equality =
  Phase.combineFirstInjective equality

sourceAcceptingImpliesPhaseAccepting :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Standard.state (Decider.finish witness formula)
    ≡ Coded.acceptingState (Decider.code witness) →
  Standard.state (candidatePhaseFinish witness formula)
    ≡ Coded.acceptingState (candidatePhaseCode witness formula)
sourceAcceptingImpliesPhaseAccepting witness formula sourceAccepting =
  cong
    (Phase.phaseTerminalState
      (Decider.code witness)
      (candidateSteps witness formula))
    sourceAccepting

candidatePhaseAcceptanceIff :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  (Standard.state (candidatePhaseFinish witness formula)
      ≡ Coded.acceptingState (candidatePhaseCode witness formula)
   → Standard.state (Decider.finish witness formula)
      ≡ Coded.acceptingState (Decider.code witness))
  ×
  (Standard.state (Decider.finish witness formula)
      ≡ Coded.acceptingState (Decider.code witness)
   → Standard.state (candidatePhaseFinish witness formula)
      ≡ Coded.acceptingState (candidatePhaseCode witness formula))
candidatePhaseAcceptanceIff witness formula =
  phaseAcceptingImpliesSourceAccepting witness formula ,
  sourceAcceptingImpliesPhaseAccepting witness formula

candidatePhaseEndpointTransitionNothing :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (candidatePhaseCode witness formula)))
    (Standard.state (candidatePhaseFinish witness formula))
    (Standard.scanned (candidatePhaseFinish witness formula))
  ≡ nothing
candidatePhaseEndpointTransitionNothing witness formula =
  Phase.terminalStandardTransitionNothing
    (Decider.code witness)
    (candidateSteps witness formula)
    (Standard.state (Decider.finish witness formula))
    (Standard.scanned (Decider.finish witness formula))

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The candidate phase is now a genuine literal finite-machine component with:
--   * exactly the original polynomial candidate step count;
--   * exactly the original tape evolution;
--   * an accepting-state equivalence back to the source candidate;
--   * a terminal dispatch key with no resident transition.
--
-- Therefore the remaining compiler no longer needs to assume a halting or
-- quiescent endpoint for arbitrary polynomial candidates.  It can sum this
-- wrapper with generator/opposite modes and attach a fresh return link.
------------------------------------------------------------------------
