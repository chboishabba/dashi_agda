module DASHI.Mathematics.Complexity.StandardMachineSpanGrowthExact where

------------------------------------------------------------------------
-- ONE STANDARD TM STEP GROWS REPRESENTED TAPE SPAN BY AT MOST ONE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Span
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

applyTransitionSpanBound :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    (configuration : Standard.StandardConfiguration machine)
    (transition : Standard.StandardTransition State Symbol) →
  Span.configurationSpan
    (Standard.standardApplyTransition machine configuration transition)
  ≤ suc (Span.configurationSpan configuration)
applyTransitionSpanBound machine
    (Standard.standard-configuration [] q a right)
    (Standard.standard-transition q' b Local.moveLeft) =
  NatP.≤-refl _
applyTransitionSpanBound machine
    (Standard.standard-configuration (l ∷ left) q a right)
    (Standard.standard-transition q' b Local.moveLeft) =
  NatP.n≤1+n _
applyTransitionSpanBound machine
    (Standard.standard-configuration left q a right)
    (Standard.standard-transition q' b Local.stayPut) =
  NatP.n≤1+n _
applyTransitionSpanBound machine
    (Standard.standard-configuration left q a [])
    (Standard.standard-transition q' b Local.moveRight) =
  NatP.≤-refl _
applyTransitionSpanBound machine
    (Standard.standard-configuration left q a (r ∷ right))
    (Standard.standard-transition q' b Local.moveRight) =
  NatP.n≤1+n _

standardStepSpanBound :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {before after : Standard.StandardConfiguration machine} →
  Standard.standardNext machine before ≡ just after →
  Span.configurationSpan after
  ≤ suc (Span.configurationSpan before)
standardStepSpanBound {machine = machine} {before = before} edge
    with Standard.transition machine
      (Standard.state before)
      (Standard.scanned before)
... | nothing = ()
... | just transition
    with edge
...   | refl =
  applyTransitionSpanBound machine before transition

standardRunSpanBound :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {steps : Nat}
    {start finish : Standard.StandardConfiguration machine} →
  Run.StandardExactRun machine steps start finish →
  Span.configurationSpan finish
  ≤ Span.configurationSpan start + steps
standardRunSpanBound Run.standardRunDone =
  NatP.≤-refl _
standardRunSpanBound
    (Run.standardRunStep {steps = steps} {current = current} edge rest) =
  NatP.≤-trans
    (standardRunSpanBound rest)
    (NatP.+-monoʳ-≤ steps (standardStepSpanBound edge))

------------------------------------------------------------------------
-- RESOURCE CONSEQUENCE
--
-- A prefix of p target-machine steps cannot increase represented span by more
-- than p. Combined with exact guarded-start spans, this distinguishes literal
-- tape geometry from the harder content-generation problem.
------------------------------------------------------------------------
