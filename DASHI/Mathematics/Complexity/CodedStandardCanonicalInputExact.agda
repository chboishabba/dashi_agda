module DASHI.Mathematics.Complexity.CodedStandardCanonicalInputExact where

------------------------------------------------------------------------
-- CANONICAL STANDARD INPUT CONFIGURATION INDEPENDENT OF ANY TIME BUDGET
--
-- Polynomial machine execution should not be defined from a tape whose finite
-- blank margin is itself parameterised by the claimed runtime.  The ordinary
-- initial row already has a unique interior head, so project that minimal row to
-- the standard split-tape carrier once and for all.  Cook guard padding remains
-- a downstream representation/quotation concern.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

initialUnique :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  WF.ExactlyOneHead (Local.cells (Input.initialInputRow input))
initialUnique input =
  Character.interiorHeadIsUnique (Input.initialInputInterior input)

canonicalStandardStart :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  Standard.StandardConfiguration (Standard.standardControlOfConcrete machine)
canonicalStandardStart input =
  Canonical.canonicalProjection (initialUnique input)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Runtime witnesses can now be tied to one input configuration independent of
-- their own step count. GuardedStandardStart(input,T) is reserved for the later
-- Cook--Levin representation of an already-fixed T-step execution.
------------------------------------------------------------------------
