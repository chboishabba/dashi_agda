module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeIntrinsicOperationalStepExact where

------------------------------------------------------------------------
-- INTRINSIC OPERATIONAL STEP ON THE ACTUAL ConcreteTapeMachine ROW
--
-- The repository already proves:
--
--   ExactlyOneHead row + HeadMargin 1 row
--     -> InteriorHeadConfiguration machine row
--
-- and the executable-window owner already proves that sequential lookup of
-- the ACTUAL machine rule table produces a literal TapeRow carrying an actual
-- MachineStep witness.
--
-- This file closes the seam between those two owners.  No caller supplies
-- prefix/left/head/right/suffix decomposition data: it is recovered from the
-- row invariant itself and then fed to the same operational rule lookup used
-- by the Cook--Levin lane.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeExecutableWindowStepExact as Window

------------------------------------------------------------------------
-- Successful intrinsic execution: output row plus a MachineStep from the
-- ORIGINAL row, not merely from a separately supplied canonical shape.
------------------------------------------------------------------------

record IntrinsicExecutedStep
    (machine : Local.ConcreteTapeMachine)
    (before : Local.TapeRow machine) : Set₁ where
  constructor intrinsic-executed-step
  field
    after : Local.TapeRow machine
    witness : Local.MachineStep machine before after

open IntrinsicExecutedStep public

executeInteriorRow :
  ∀ {machine row} →
  Character.InteriorHeadConfiguration machine row →
  Maybe (IntrinsicExecutedStep machine row)
executeInteriorRow {machine} {row} interior
    with Character.rowShape interior
... | refl
    with Interpreter.fetchConcreteRule
      machine
      (Character.headState interior)
      (Character.readSymbol interior)
...   | nothing = nothing
...   | just matched =
  just
    (intrinsic-executed-step
      (Window.afterRowForRule
        machine
        (Character.prefix interior)
        (Character.leftSymbol interior)
        (Character.rightSymbol interior)
        (Character.suffix interior)
        (Interpreter.rule matched))
      (Window.listedMatchingRuleIsMachineStep
        machine
        (Character.prefix interior)
        (Character.leftSymbol interior)
        (Character.headState interior)
        (Character.readSymbol interior)
        (Character.rightSymbol interior)
        (Character.suffix interior)
        (Interpreter.rule matched)
        (Interpreter.occurs matched)
        (Interpreter.sourceExact matched)
        (Interpreter.readExact matched)))

------------------------------------------------------------------------
-- Canonical row parsing is now consumed directly:
--
--   ExactlyOneHead + one-cell margin
--     -> InteriorHeadConfiguration
--     -> executable actual-row step.
------------------------------------------------------------------------

executeUniqueMarginRow :
  ∀ {machine row} →
  WF.ExactlyOneHead (Local.cells row) →
  Margin.HeadMargin 1 (Local.cells row) →
  Maybe (IntrinsicExecutedStep machine row)
executeUniqueMarginRow unique margin =
  executeInteriorRow
    (Margin.interiorFromUniqueMargin unique margin)

------------------------------------------------------------------------
-- A successful result is propositionally an actual machine step.  This is
-- deliberately stated on the output package so downstream iteration never
-- needs to reopen the parser implementation.
------------------------------------------------------------------------

intrinsicExecutionSound :
  ∀ {machine row}
    {unique : WF.ExactlyOneHead (Local.cells row)}
    {margin : Margin.HeadMargin 1 (Local.cells row)}
    {result : IntrinsicExecutedStep machine row} →
  executeUniqueMarginRow unique margin ≡ just result →
  Local.MachineStep machine row (after result)
intrinsicExecutionSound {result = result} refl =
  witness result

------------------------------------------------------------------------
-- The output retains the existing exactly-one-head theorem whenever the
-- selected step is upgraded to the repository's well-formed occurrence.
--
-- The raw MachineStep relation itself does not require plain context, so that
-- extra producer remains intentionally separate.  In the guarded Cook--Levin
-- lane, those well-formedness proofs are already supplied by the locality
-- reconstruction owners.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID:
-- * row-intrinsic parser from ExactlyOneHead + HeadMargin 1 (reused);
-- * no externally supplied local-window decomposition in the operational API;
-- * literal sequential lookup on ConcreteTapeMachine.rules;
-- * successful intrinsic execution yields an actual MachineStep from the
--   original TapeRow;
-- * soundness theorem for the intrinsic executable step.
--
-- IMPORTANT EXISTING CLOSURE:
-- * guarded Cook--Levin rows already carry decreasing HeadMargin and are
--   iterated as WellFormedMachineStep objects by ConcreteTapeDecodedRunInduction;
-- * SAT -> accepting run is already proved by
--   ConcreteTapeSATToAcceptingRunExact.
--
-- STILL OPEN:
-- * a converse "every MachineStep is the result of this executable function"
--   requires a deterministic/first-match compatibility condition on duplicate
--   rule keys, because raw MachineStep permits any listed matching rule;
-- * standard TM <-> ConcreteTapeMachine polynomial simulations;
-- * transport of polynomial clocks;
-- * universal SAT lower-bound obstruction.
------------------------------------------------------------------------
