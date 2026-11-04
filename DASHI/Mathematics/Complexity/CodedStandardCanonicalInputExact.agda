module DASHI.Mathematics.Complexity.CodedStandardCanonicalInputExact where

------------------------------------------------------------------------
-- CANONICAL STANDARD INPUT CONFIGURATION INDEPENDENT OF ANY TIME BUDGET
--
-- Conventional split-tape semantics already interprets an empty side list as
-- an infinite blank tail.  Therefore operational input should not inherit the
-- concrete Cook row's explicit boundary blanks:
--
--   []       -> ([], q0, blank, [])
--   a :: xs  -> ([], q0, a, xs)
--
-- Cook's finite guarded row is a downstream representation of this same tape,
-- not part of the definition of polynomial runtime.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

canonicalStandardStart :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  Standard.StandardConfiguration (Standard.standardControlOfConcrete machine)
canonicalStandardStart {machine} [] =
  Standard.standard-configuration
    []
    (Local.initialState machine)
    (Local.blank machine)
    []
canonicalStandardStart {machine} (symbol ∷ rest) =
  Standard.standard-configuration
    []
    (Local.initialState machine)
    symbol
    rest

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Runtime now starts from the standard mathematical tape representation with
-- implicit blank tails. Any finite explicit margin used by Cook--Levin must be
-- connected through blank-tail equivalence, not treated as part of runtime.
------------------------------------------------------------------------
