module DASHI.Mathematics.Complexity.PNotEqualsNPActualMachineStutteringTransportExact where

------------------------------------------------------------------------
-- A LITERAL OPERATIONAL TRANSFORMATION OF A DETERMINISTIC MACHINE
--
-- Given the actual deterministic machine transition function:
--
--     c -> Maybe c
--
-- insert one explicitly represented intermediate configuration:
--
--     ready c -> pending c -> ready (next c).
--
-- If next c = nothing, the pending configuration halts with nothing.
-- The transformed machine has the SAME input language and output, and
-- exactly TWO transitions per original transition (including failed steps).
--
-- This construction is generic over the original Machine, not restricted
-- to a 3^k state carrier. It transports the candidate's actual configuration
-- and its actual transition.
--
-- All step costs are counted within the repository's abstract transition
-- semantics. One original step may itself evaluate an arbitrary extensional
-- function; hence this is NOT yet a physical-tape time-preservation theorem,
-- and it establishes NO SAT time lower bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine
import DASHI.Mathematics.Complexity.DeterministicMachineToInPExact as ToP
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPExtensionalCandidateAbstractMachineExact as Candidate

------------------------------------------------------------------------
-- The entire original configuration is retained, with a one-bit phase.
------------------------------------------------------------------------

data StutteringConfiguration
    (configuration : Set) : Set where
  ready : configuration → StutteringConfiguration configuration
  pending : configuration → StutteringConfiguration configuration

stutteringStep :
  ∀ {configuration : Set} →
  (configuration → Maybe configuration) →
  StutteringConfiguration configuration →
  Maybe (StutteringConfiguration configuration)
stutteringStep next (ready c) =
  just (pending c)
stutteringStep next (pending c) with next c
... | nothing = nothing
... | just successor = just (ready successor)

stutteringMachine :
  (machine : Machine.DeterministicMachine) →
  Machine.DeterministicMachine
stutteringMachine machine = record
  { Machine.dInput = Machine.dInput machine
  ; Machine.dConfiguration =
      StutteringConfiguration (Machine.dConfiguration machine)
  ; Machine.dInitial =
      λ input → ready (Machine.dInitial machine input)
  ; Machine.dNext =
      stutteringStep (Machine.dNext machine)
  ; Machine.dAccepting =
      λ where
        (ready c) → Machine.dAccepting machine c
        (pending c) → ⊥
  }

------------------------------------------------------------------------
-- No pending phase can invent an accepting event. Only ready states have
-- observable acceptance, matching the untransformed configuration.
------------------------------------------------------------------------

readyAcceptanceExact :
  (machine : Machine.DeterministicMachine)
  (c : Machine.dConfiguration machine) →
  Machine.dAccepting (stutteringMachine machine) (ready c)
  ≡ Machine.dAccepting machine c
readyAcceptanceExact machine c = refl

pendingCannotAccept :
  (machine : Machine.DeterministicMachine)
  (c : Machine.dConfiguration machine) →
  Machine.dAccepting (stutteringMachine machine) (pending c)
  → ⊥
pendingCannotAccept machine c ()

------------------------------------------------------------------------
-- Transition-level observations differ during the pending phase. This
-- construction preserves accepting events after each complete two-step
-- segment; it does NOT claim literal equality of uncompressed traces.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Exact step accounting for arbitrary original traces.
------------------------------------------------------------------------

doubleSteps : Nat → Nat
doubleSteps zero = zero
doubleSteps (suc steps) = suc (suc (doubleSteps steps))

readyMaybe :
  ∀ {configuration : Set} →
  Maybe configuration →
  Maybe (StutteringConfiguration configuration)
readyMaybe nothing = nothing
readyMaybe (just c) = just (ready c)

stutteringRunExact :
  (machine : Machine.DeterministicMachine)
  (steps : Nat)
  (configuration : Machine.dConfiguration machine) →
  Machine.iterateDeterministic
    (stutteringMachine machine)
    (doubleSteps steps)
    (ready configuration)
  ≡
  readyMaybe
    (Machine.iterateDeterministic machine steps configuration)
stutteringRunExact machine zero configuration = refl
stutteringRunExact machine (suc steps) configuration
  with Machine.dNext machine configuration
... | nothing = refl
... | just successor =
  stutteringRunExact machine steps successor

------------------------------------------------------------------------
-- A clocked Boolean execution stays an execution of the transformed
-- machine, with the doubled clock and identical final Boolean answer.
------------------------------------------------------------------------

stutteringExecution :
  ∀ {machine : Machine.DeterministicMachine} →
  (execution : ToP.ClockedDeterministicBooleanExecution machine) →
  ToP.ClockedDeterministicBooleanExecution
    (stutteringMachine machine)
stutteringExecution {machine} execution = record
  { ToP.inputLength = ToP.inputLength execution
  ; ToP.clock =
      λ inputSize →
        doubleSteps (ToP.clock execution inputSize)
  ; ToP.finalConfiguration =
      λ input → ready (ToP.finalConfiguration execution input)
  ; ToP.runExact =
      λ input →
        trans
          (stutteringRunExact machine
            (ToP.clock execution (ToP.inputLength execution input))
            (Machine.dInitial machine input))
          (cong readyMaybe (ToP.runExact execution input))
  ; ToP.output =
      λ where
        (ready c) → ToP.output execution c
        (pending c) → false
  }

stutteringPreservesDecision :
  ∀ {machine : Machine.DeterministicMachine}
    (execution : ToP.ClockedDeterministicBooleanExecution machine)
    (input : Machine.dInput machine) →
  ToP.clockedDecision (stutteringExecution execution) input
  ≡
  ToP.clockedDecision execution input
stutteringPreservesDecision execution input = refl

------------------------------------------------------------------------
-- An actual polynomial SAT candidate gets this transport immediately.
-- The resource statement is EXACTLY a doubled abstract machine clock,
-- NOT a finite-program execution-cost theorem.
------------------------------------------------------------------------

stutterCandidateDecisionExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (formula : Cook.BooleanFormula) →
  ToP.clockedDecision
    (stutteringExecution (Candidate.candidateMachineExecution candidate))
    formula
  ≡
  Direct.decide candidate formula
stutterCandidateDecisionExact candidate formula =
  trans
    (stutteringPreservesDecision
      (Candidate.candidateMachineExecution candidate)
      formula)
    (Candidate.candidateMachineDecisionExact candidate formula)

stutterCandidateClockIsTwo :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (formula : Cook.BooleanFormula) →
  ToP.clock
    (stutteringExecution (Candidate.candidateMachineExecution candidate))
    (ToP.inputLength (Candidate.candidateMachineExecution candidate) formula)
  ≡ suc (suc zero)
stutterCandidateClockIsTwo candidate formula = refl

------------------------------------------------------------------------
-- CLAY BOUNDARY
--
-- This proves output and abstract transition preservation with a measured
-- 2x cost on the actual machine object. Such a polynomial-overhead
-- transformation exists and cannot itself obstruct P=NP.
--
-- A genuine SAT lower-bound argument must use finite, fully costed machine
-- realizations and find a universally unavoidable obstruction. Restricted
-- ordered residual width and an abstract one-step oracle cannot supply it.
------------------------------------------------------------------------
