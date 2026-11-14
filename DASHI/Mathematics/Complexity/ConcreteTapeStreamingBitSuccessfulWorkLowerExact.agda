module DASHI.Mathematics.Complexity.ConcreteTapeStreamingBitSuccessfulWorkLowerExact where

------------------------------------------------------------------------
-- SUCCESSFUL INDEXED ACCESS HAS AN INTRINSIC LINEAR LOWER BOUND
--
-- The costed bit cursor consumes one `nextBitCosted` phase for every skipped bit
-- and one final phase for the requested bit.  Therefore a successful query at
-- index i cannot cost fewer than i+1 cursor work units.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitCostedExact as Costed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Every next-bit phase pays at least one unit, independent of branch.
------------------------------------------------------------------------

nextBitCostedPositive :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  suc zero ≤
    Costed.work
      (Costed.nextBitCosted
        stateCoverage symbolCoverage nonempty
        steps cols initialTarget state)
nextBitCostedPositive
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needToken tokenState)
  with Costed.nextTokenCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
... | Costed.costed tokenResult tokenWork = s≤s z≤n
nextBitCostedPositive
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needSecond token nextState) = s≤s z≤n
nextBitCostedPositive
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needThird token nextState) = s≤s z≤n
nextBitCostedPositive
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    Cursor.bitDone = s≤s z≤n

------------------------------------------------------------------------
-- A successful bit-at run cannot terminate early.
------------------------------------------------------------------------

bitAtCostedSuccessfulWorkLower :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat)
    (state : Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols))
    (bit : Bool) →
  Costed.result
      (Costed.bitAtCosted
        stateCoverage symbolCoverage nonempty
        steps cols initialTarget index state)
    ≡ just bit →
  suc index ≤
    Costed.work
      (Costed.bitAtCosted
        stateCoverage symbolCoverage nonempty
        steps cols initialTarget index state)
bitAtCostedSuccessfulWorkLower
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    zero state bit success
  with Costed.nextBitCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget state
     | nextBitCostedPositive
        stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | Costed.costed nothing stepWork | positive
  with success
... | ()
... | Costed.costed (just (found , nextState)) stepWork | positive =
  positive
bitAtCostedSuccessfulWorkLower
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (suc index) state bit success
  with Costed.nextBitCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget state
     | nextBitCostedPositive
        stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | Costed.costed nothing stepWork | positive
  with success
... | ()
... | Costed.costed (just (found , nextState)) stepWork | positive
  with Costed.bitAtCosted
      stateCoverage symbolCoverage nonempty
      steps cols initialTarget index nextState
     | bitAtCostedSuccessfulWorkLower
        stateCoverage symbolCoverage nonempty
        steps cols initialTarget index nextState bit success
... | Costed.costed restResult restWork | recursive =
  NatP.+-mono-≤ positive recursive

------------------------------------------------------------------------
-- Specialization to the public streamed entry point.
------------------------------------------------------------------------

streamedCookBitSuccessfulWorkLower :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat)
    (bit : Bool) →
  Costed.result
      (Costed.streamedCookBitCosted
        stateCoverage symbolCoverage nonempty
        steps cols initialTarget index)
    ≡ just bit →
  suc index ≤
    Costed.work
      (Costed.streamedCookBitCosted
        stateCoverage symbolCoverage nonempty
        steps cols initialTarget index)
streamedCookBitSuccessfulWorkLower
    stateCoverage symbolCoverage nonempty steps cols initialTarget index bit =
  bitAtCostedSuccessfulWorkLower
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    index
    (Cursor.needToken (Cursor.cnfAt zero))
    bit

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The fixed-description linear upper bound is not merely an artefact of a loose
-- analysis: successful access intrinsically pays at least one cursor phase per
-- skipped/output bit.  Any standard-TM compiler may multiply this by a fixed
-- simulation factor, but cannot compile indexed access to sublinear work in i
-- while preserving this exact evaluator step-for-step.
------------------------------------------------------------------------
