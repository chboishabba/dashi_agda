module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateConfigurationFutureTransportNoGoExact where

------------------------------------------------------------------------
-- PRESENT OBSERVATION IS NOT A FUTURE-SAFE MACHINE QUOTIENT
--
-- The source machine is the ACTUAL extensional candidate machine, not a
-- ternary/nine-cell surrogate. Its configuration space is
--
--    start formula | done bit
--
-- and its transition is
--    start formula -> just (done (candidate.decide formula))
--    done bit     -> nothing.
--
-- start phi and done false have identical current Bool output, but their
-- next-step behaviors differ for EVERY candidate and EVERY formula.
--
-- Hence the context-indexed present-output fibre is not a congruence for
-- operational transport, even on the exact candidate-quoted Q2 root.
--
-- This does NOT imply any SAT time lower bound. In particular this abstract
-- one-step machine evaluates an arbitrary extensional decider in ONE step,
-- so it is not a finite-program/tape-machine cost realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine
import DASHI.Mathematics.Complexity.DeterministicMachineToInPExact as ToP
import DASHI.Mathematics.Complexity.PNotEqualsNPExtensionalCandidateAbstractMachineExact as CandidateMachine
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2

------------------------------------------------------------------------
-- Actual present output and actual candidate transition.
------------------------------------------------------------------------

candidatePresentOutput :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  CandidateMachine.CandidateConfiguration →
  Bool
candidatePresentOutput candidate =
  ToP.output (CandidateMachine.candidateMachineExecution candidate)

candidateTransition :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  CandidateMachine.CandidateConfiguration →
  Maybe CandidateMachine.CandidateConfiguration
candidateTransition candidate =
  Machine.dNext (CandidateMachine.candidateMachine candidate)

------------------------------------------------------------------------
-- Present output collisions with diverging operational futures.
------------------------------------------------------------------------

startAndDoneHaveEqualPresentOutput :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (formula : Cook.BooleanFormula) →
  candidatePresentOutput candidate (CandidateMachine.start formula)
  ≡
  candidatePresentOutput candidate (CandidateMachine.done false)
startAndDoneHaveEqualPresentOutput candidate formula = refl

startHasOperationalSuccessor :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (formula : Cook.BooleanFormula) →
  candidateTransition candidate (CandidateMachine.start formula)
  ≡
  just
    (CandidateMachine.done (Direct.decide candidate formula))
startHasOperationalSuccessor candidate formula = refl

doneHasNoOperationalSuccessor :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  candidateTransition candidate (CandidateMachine.done false)
  ≡ nothing
doneHasNoOperationalSuccessor candidate = refl

presentOutputDoesNotDetermineFutureStep :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (formula : Cook.BooleanFormula) →
  candidateTransition candidate (CandidateMachine.start formula)
  ≡
  candidateTransition candidate (CandidateMachine.done false) →
  ⊥
presentOutputDoesNotDetermineFutureStep candidate formula ()

------------------------------------------------------------------------
-- No quotient transition depending ONLY on the current output Bool can
-- compute the actual machine's Maybe-valued next configuration.
------------------------------------------------------------------------

noFutureFactorizationThroughPresentOutput :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (formula : Cook.BooleanFormula)
    (advance : Bool → Maybe CandidateMachine.CandidateConfiguration) →
  ((configuration : CandidateMachine.CandidateConfiguration) →
    candidateTransition candidate configuration
    ≡ advance (candidatePresentOutput candidate configuration)) →
  ⊥
noFutureFactorizationThroughPresentOutput
    candidate formula advance factors =
  presentOutputDoesNotDetermineFutureStep
    candidate formula
    (trans
      (factors (CandidateMachine.start formula))
      (trans
        (cong advance
          (startAndDoneHaveEqualPresentOutput candidate formula))
        (sym (factors (CandidateMachine.done false)))))

------------------------------------------------------------------------
-- The witness is also the LITERAL candidate-derived Q2 root: no unrelated
-- synthetic formula is selected for the collision.
------------------------------------------------------------------------

candidateQuotedRootOutputTransportFails :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (state : Q2.BoundedSelfReferenceState)
    (advance : Bool → Maybe CandidateMachine.CandidateConfiguration) →
  ((configuration : CandidateMachine.CandidateConfiguration) →
    candidateTransition candidate configuration
    ≡ advance (candidatePresentOutput candidate configuration)) →
  ⊥
candidateQuotedRootOutputTransportFails candidate state advance =
  noFutureFactorizationThroughPresentOutput
    candidate (Q2.currentFormula state) advance

------------------------------------------------------------------------
-- INTERPRETATION
--
-- This proves that the present-output observation is insufficient for the
-- full operational consumer; it does not prove that ALL compressed machine
-- configurations are insufficient, or that the candidate must build Q1.
-- A successful fibre/braid transport must preserve the genuine successor
-- structure AND pay for its own representation and operations.
------------------------------------------------------------------------
