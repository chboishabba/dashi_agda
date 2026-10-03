module DASHI.Mathematics.Complexity.ConcreteTapeStandardClockExact where

------------------------------------------------------------------------
-- CLOCK TRANSPORT FOR THE CONCRETE <-> CONVENTIONAL STANDARD TM BRIDGE
--
-- `ConcreteTapeStandardRunExact` already proves one standard step for every
-- concrete edge.  This owner packages the resulting complexity statement
-- against the literal first-match rule-table interpreter:
--
--   * projected step count is exactly the concrete run length;
--   * accumulated dispatch work is <= T * |rules|;
--   * the guarded concrete tape window has inputWidth + 2*T cells.
--
-- Thus the forward Concrete -> standard model translation has an explicit
-- linear/polynomial clock receipt with no hidden extensional transition oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Bridge
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard

------------------------------------------------------------------------
-- Literal standard run length, read back from the inductive run witness.
------------------------------------------------------------------------

standardRunLengthIndexed :
  ∀ {State Symbol machine steps start finish} →
  Bridge.StandardExactRun {State} {Symbol} machine steps start finish → Nat
standardRunLengthIndexed Bridge.standardRunDone = zero
standardRunLengthIndexed (Bridge.standardRunStep edge rest) =
  suc (standardRunLengthIndexed rest)

standardRunLengthIndexed_exact :
  ∀ {State Symbol machine steps start finish}
    (run : Bridge.StandardExactRun {State} {Symbol} machine steps start finish) →
  standardRunLengthIndexed run ≡ steps
standardRunLengthIndexed_exact Bridge.standardRunDone = refl
standardRunLengthIndexed_exact (Bridge.standardRunStep edge rest)
  rewrite standardRunLengthIndexed_exact rest = refl

------------------------------------------------------------------------
-- Accumulated literal dispatch work along an exact conventional run whose
-- control function is the existing concrete first-match scan.
------------------------------------------------------------------------

standardRunDispatchWork :
  ∀ {machine steps start finish} →
  Bridge.StandardExactRun
    (Standard.standardControlOfConcrete machine)
    steps start finish →
  Nat
standardRunDispatchWork Bridge.standardRunDone = zero
standardRunDispatchWork
    {machine = machine}
    (Bridge.standardRunStep {current = current} edge rest) =
  Interpreter.fetchConcreteRuleWork
      machine
      (Standard.state current)
      (Standard.scanned current)
    + standardRunDispatchWork rest

standardRunDispatchWorkBound :
  ∀ {machine steps start finish}
    (run : Bridge.StandardExactRun
      (Standard.standardControlOfConcrete machine)
      steps start finish) →
  standardRunDispatchWork run
    ≤ steps * Canonical.listLength (Local.rules machine)
standardRunDispatchWorkBound Bridge.standardRunDone =
  NatP.≤-refl zero
standardRunDispatchWorkBound
    {machine = machine}
    (Bridge.standardRunStep {steps = steps} {current = current} edge rest) =
  NatP.+-mono-≤
    (Interpreter.fetchConcreteRuleWorkBound
      machine (Standard.state current) (Standard.scanned current))
    (standardRunDispatchWorkBound rest)

------------------------------------------------------------------------
-- Exact step-clock preservation for the concrete run projection.
------------------------------------------------------------------------

projectedStepClockIdentity :
  ∀ {machine start rows finish}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (concreteRun : Run.WellFormedTapeRun machine start rows finish) →
  let projected =
        Bridge.projectWellFormedTapeRun deterministic startUnique concreteRun
  in standardRunLengthIndexed (Bridge.standardRun projected)
      ≡ Run.runLength concreteRun
projectedStepClockIdentity deterministic startUnique concreteRun =
  standardRunLengthIndexed_exact
    (Bridge.standardRun
      (Bridge.projectWellFormedTapeRun deterministic startUnique concreteRun))

------------------------------------------------------------------------
-- Static polynomial-overhead receipt.
------------------------------------------------------------------------

record ConcreteStandardClockReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    exactStepClockPaid :
      ∀ {steps start finish}
        (run : Bridge.StandardExactRun
          (Standard.standardControlOfConcrete machine)
          steps start finish) →
      standardRunLengthIndexed run ≡ steps

    dispatchWorkLinearPaid :
      ∀ {steps start finish}
        (run : Bridge.StandardExactRun
          (Standard.standardControlOfConcrete machine)
          steps start finish) →
      standardRunDispatchWork run
        ≤ steps * Canonical.listLength (Local.rules machine)

    guardedTapeWidthLinearPaid :
      ∀ (input : Input.InputWord machine)
        (steps : Nat) →
      Coordinate.listLength (Guard.guardedInitialCells input steps)
      ≡ Input.initialInputCellCount input + (2 * steps)

concreteStandardClockReceipt :
  (machine : Local.ConcreteTapeMachine) →
  ConcreteStandardClockReceipt machine
concreteStandardClockReceipt machine = record
  { exactStepClockPaid = standardRunLengthIndexed_exact
  ; dispatchWorkLinearPaid = standardRunDispatchWorkBound
  ; guardedTapeWidthLinearPaid = Guard.guardedInitialCellCount
  }

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID HERE (subject to exact-head Agda certification):
-- * exact equality of concrete and standard step clocks on projected runs;
-- * accumulated first-match dispatch work <= T * |rules|;
-- * finite concrete tape width = input width + 2T;
-- * therefore the already-constructed Concrete -> standard simulation has
--   explicit linear/polynomial overhead with no hidden transition oracle.
--
-- REMAINING ORDINARY MODEL-INVARIANCE SEAM:
-- * reconstruct a guarded concrete run from a standard run of the same finite
--   presentation, then package accepting-language iff;
-- * after that, freeze machine-representation infrastructure.
------------------------------------------------------------------------
