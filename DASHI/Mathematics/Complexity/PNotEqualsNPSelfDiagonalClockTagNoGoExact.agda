module DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalClockTagNoGoExact where

------------------------------------------------------------------------
-- CLOCK-TAGGING NO-GO FOR RAW CONFIGURATION SHARING
--
-- A universal P != NP lower-bound invariant cannot depend on repeated exact
-- machine configurations.  Any deterministic machine M may be replaced by
--
--   M^ : configuration = Nat × configuration(M)
--
-- whose transition increments an irrelevant clock coordinate while performing
-- exactly the same original transition.
--
-- Along an execution, the clock tag changes at every step.  Hence distinct
-- times cannot have equal tagged configurations, while the accepted language
-- and the ClockedDeterministicBooleanExecution decision function are preserved.
--
-- The construction is repo-native.  It uses the existing deterministic-machine
-- and machine->InP carriers; no external source is attributed this theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; _≢_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine
import DASHI.Mathematics.Complexity.DeterministicMachineToInPExact as ToP
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

------------------------------------------------------------------------
-- Clock-tagged machine.
------------------------------------------------------------------------

clockTaggedNext :
  ∀ {machine : Machine.DeterministicMachine} →
  Nat × Machine.dConfiguration machine →
  Maybe (Nat × Machine.dConfiguration machine)
clockTaggedNext {machine} (time , configuration)
    with Machine.dNext machine configuration
... | nothing = nothing
... | just successor = just (suc time , successor)

clockTagMachine :
  Machine.DeterministicMachine →
  Machine.DeterministicMachine
clockTagMachine machine = record
  { Machine.dInput = Machine.dInput machine
  ; Machine.dConfiguration =
      Nat × Machine.dConfiguration machine
  ; Machine.dInitial =
      λ input → zero , Machine.dInitial machine input
  ; Machine.dNext = clockTaggedNext
  ; Machine.dAccepting =
      λ tagged → Machine.dAccepting machine (proj₂ tagged)
  }

projectTaggedConfiguration :
  ∀ {machine : Machine.DeterministicMachine} →
  Machine.dConfiguration (clockTagMachine machine) →
  Machine.dConfiguration machine
projectTaggedConfiguration = proj₂

clockTaggedTransitionProjects :
  ∀ {machine : Machine.DeterministicMachine}
    {time : Nat}
    {configuration successor : Machine.dConfiguration machine} →
  clockTaggedNext {machine} (time , configuration)
    ≡ just (suc time , successor) →
  Machine.dNext machine configuration ≡ just successor
clockTaggedTransitionProjects {machine} {time} {configuration} {successor}
    taggedStep
    with Machine.dNext machine configuration
... | nothing = impossible taggedStep
  where
    impossible :
      nothing ≡ just (suc time , successor) →
      Machine.dNext machine configuration ≡ just successor
    impossible ()
... | just actual
    with taggedStep
... | refl = refl

------------------------------------------------------------------------
-- Exact run transport.
------------------------------------------------------------------------

advanceClock : Nat → Nat → Nat
advanceClock time zero = time
advanceClock time (suc steps) =
  suc (advanceClock time steps)

advanceClockSucStart :
  (time steps : Nat) →
  advanceClock (suc time) steps
  ≡ suc (advanceClock time steps)
advanceClockSucStart time zero = refl
advanceClockSucStart time (suc steps)
    rewrite advanceClockSucStart time steps =
  refl

advanceClockZero : (steps : Nat) → advanceClock zero steps ≡ steps
advanceClockZero zero = refl
advanceClockZero (suc steps)
    rewrite advanceClockZero steps =
  refl

clockTaggedRunFromOriginal :
  ∀ {machine : Machine.DeterministicMachine}
    (time steps : Nat)
    (start finish : Machine.dConfiguration machine) →
  Machine.iterateDeterministic machine steps start ≡ just finish →
  Machine.iterateDeterministic
    (clockTagMachine machine)
    steps
    (time , start)
  ≡ just (advanceClock time steps , finish)
clockTaggedRunFromOriginal time zero start finish run
    with run
... | refl = refl
clockTaggedRunFromOriginal {machine} time (suc steps) start finish run
    with Machine.dNext machine start
... | nothing = impossible run
  where
    impossible :
      nothing ≡ just finish →
      Machine.iterateDeterministic
        (clockTagMachine machine)
        (suc steps)
        (time , start)
      ≡ just (advanceClock time (suc steps) , finish)
    impossible ()
... | just middle
    rewrite advanceClockSucStart time steps =
  clockTaggedRunFromOriginal
    (suc time)
    steps
    middle
    finish
    run

clockTaggedRunProjectsToOriginalRun :
  ∀ {machine : Machine.DeterministicMachine}
    (time steps : Nat)
    (start : Machine.dConfiguration machine)
    (taggedFinish :
      Machine.dConfiguration (clockTagMachine machine)) →
  Machine.iterateDeterministic
    (clockTagMachine machine)
    steps
    (time , start)
  ≡ just taggedFinish →
  Machine.iterateDeterministic
    machine
    steps
    start
  ≡ just (projectTaggedConfiguration taggedFinish)
clockTaggedRunProjectsToOriginalRun
    {machine} time zero start taggedFinish taggedRun
    with taggedRun
... | refl = refl
clockTaggedRunProjectsToOriginalRun
    {machine} time (suc steps) start taggedFinish taggedRun
    with Machine.dNext machine start
... | nothing = impossible taggedRun
  where
    impossible :
      nothing ≡ just taggedFinish →
      Machine.iterateDeterministic machine (suc steps) start
      ≡ just (projectTaggedConfiguration taggedFinish)
    impossible ()
... | just middle =
  clockTaggedRunProjectsToOriginalRun
    (suc time)
    steps
    middle
    taggedFinish
    taggedRun

------------------------------------------------------------------------
-- Distinct clock values force distinct exact tagged configurations.
------------------------------------------------------------------------

differentTimesGiveDifferentTaggedConfigurations :
  ∀ {machine : Machine.DeterministicMachine}
    {leftTime rightTime : Nat}
    {leftConfiguration rightConfiguration :
      Machine.dConfiguration machine} →
  leftTime ≢ rightTime →
  (leftTime , leftConfiguration)
    ≢ (rightTime , rightConfiguration)
differentTimesGiveDifferentTaggedConfigurations
    different sameTagged =
  different (cong proj₁ sameTagged)

------------------------------------------------------------------------
-- Acceptance ignores the decoration.
------------------------------------------------------------------------

clockTaggedAcceptanceIsOriginalAcceptance :
  ∀ {machine : Machine.DeterministicMachine}
    (time : Nat)
    (configuration : Machine.dConfiguration machine) →
  Machine.dAccepting
      (clockTagMachine machine)
      (time , configuration)
  →
  Machine.dAccepting machine configuration
clockTaggedAcceptanceIsOriginalAcceptance time configuration accepting =
  accepting

originalAcceptanceIsClockTaggedAcceptance :
  ∀ {machine : Machine.DeterministicMachine}
    (time : Nat)
    (configuration : Machine.dConfiguration machine) →
  Machine.dAccepting machine configuration
  →
  Machine.dAccepting
      (clockTagMachine machine)
      (time , configuration)
originalAcceptanceIsClockTaggedAcceptance time configuration accepting =
  accepting

------------------------------------------------------------------------
-- Clocked Boolean execution transport.
--
-- The tagged execution has the same input length, same clock and same Boolean
-- output after projecting away the decoration.
------------------------------------------------------------------------

clockTagExecution :
  ∀ {machine : Machine.DeterministicMachine} →
  ToP.ClockedDeterministicBooleanExecution machine →
  ToP.ClockedDeterministicBooleanExecution (clockTagMachine machine)
clockTagExecution {machine} execution = record
  { ToP.inputLength = ToP.inputLength execution
  ; ToP.clock = ToP.clock execution
  ; ToP.finalConfiguration =
      λ input →
        ToP.clock execution (ToP.inputLength execution input)
        ,
        ToP.finalConfiguration execution input
  ; ToP.runExact =
      λ input →
        taggedRunExact input
  ; ToP.output =
      λ tagged →
        ToP.output execution (proj₂ tagged)
  }
  where
    taggedRunExact :
      (input : Machine.dInput machine) →
      Machine.iterateDeterministic
        (clockTagMachine machine)
        (ToP.clock execution (ToP.inputLength execution input))
        (Machine.dInitial (clockTagMachine machine) input)
      ≡
      just
        ( ToP.clock execution (ToP.inputLength execution input)
        , ToP.finalConfiguration execution input
        )
    taggedRunExact input
      rewrite
        sym
          (advanceClockZero
            (ToP.clock execution
              (ToP.inputLength execution input))) =
      clockTaggedRunFromOriginal
        zero
        (ToP.clock execution (ToP.inputLength execution input))
        (Machine.dInitial machine input)
        (ToP.finalConfiguration execution input)
        (ToP.runExact execution input)

clockTaggedMachinePreservesDecision :
  ∀ {machine : Machine.DeterministicMachine}
    (execution : ToP.ClockedDeterministicBooleanExecution machine)
    (input : Machine.dInput machine) →
  ToP.clockedDecision (clockTagExecution execution) input
  ≡
  ToP.clockedDecision execution input
clockTaggedMachinePreservesDecision execution input =
  refl

clockTaggedMachinePreservesPolynomialTime :
  ∀ {machine : Machine.DeterministicMachine}
    {cost : PR.PolynomialCostModel (Machine.dInput machine)}
    (execution : ToP.ClockedDeterministicBooleanExecution machine) →
  ToP.ClockedExecutionCostRealization cost execution →
  ToP.ClockedExecutionCostRealization
    cost
    (clockTagExecution execution)
clockTaggedMachinePreservesPolynomialTime execution realization = record
  { ToP.clockPolynomiallyBounded =
      ToP.clockPolynomiallyBounded realization
  ; ToP.exactEvaluatorPolynomial =
      ToP.exactEvaluatorPolynomial realization
  }

clockTaggedExecutionGivesSameInPDecision :
  ∀ {machine : Machine.DeterministicMachine}
    {cost : PR.PolynomialCostModel (Machine.dInput machine)}
    (execution : ToP.ClockedDeterministicBooleanExecution machine)
    (realization : ToP.ClockedExecutionCostRealization cost execution) →
  PR.InP cost (ToP.clockedLanguage (clockTagExecution execution))
clockTaggedExecutionGivesSameInPDecision execution realization =
  ToP.clockedExecutionGivesInP
    (clockTagExecution execution)
    (clockTaggedMachinePreservesPolynomialTime
      execution realization)

------------------------------------------------------------------------
-- Conclusion.
--
-- Exact tagged configuration equality at two distinct clock values is
-- impossible, while the clocked Boolean decision and its polynomial-time
-- realization are preserved.  Therefore a universal lower-bound argument
-- cannot require repeated exact raw machine configurations; such recurrence is
-- not invariant under polynomial-time language-preserving implementation
-- decoration.
------------------------------------------------------------------------
