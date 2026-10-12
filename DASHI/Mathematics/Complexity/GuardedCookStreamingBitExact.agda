module DASHI.Mathematics.Complexity.GuardedCookStreamingBitExact where

------------------------------------------------------------------------
-- CANONICAL GUARDED COOK QUERY = LIST-FREE STREAMED BIT CURSOR
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitExact as Exact

streamedQueryBit :
  Query.GuardedCookBitQuery →
  Maybe Agda.Builtin.Bool.Bool
streamedQueryBit query =
  Cursor.streamedCookBit
    (Coded.codedStateCoverage (Query.code query))
    (Coded.codedSymbolCoverage (Query.code query))
    (Query.nonemptyRules query)
    (Query.steps query)
    (Guard.guardedInitialCols
      (Query.input query)
      (Query.steps query))
    (Sound.guardedInitialBits
      (Coded.codedStateCoverage (Query.code query))
      (Coded.codedSymbolCoverage (Query.code query))
      (Query.input query)
      (Query.steps query))
    (Query.index query)

streamedQueryBitExact :
  (query : Query.GuardedCookBitQuery) →
  streamedQueryBit query
  ≡ Semantics.queryAnswer query
streamedQueryBitExact query =
  Exact.streamedCookBitExact
    (Coded.codedStateCoverage (Query.code query))
    (Coded.codedSymbolCoverage (Query.code query))
    (Query.nonemptyRules query)
    (Query.steps query)
    (Guard.guardedInitialCols
      (Query.input query)
      (Query.steps query))
    (Sound.guardedInitialBits
      (Coded.codedStateCoverage (Query.code query))
      (Coded.codedSymbolCoverage (Query.code query))
      (Query.input query)
      (Query.steps query))
    (Query.index query)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The canonical answer-blind `(coded machine,input,T,index)` query now has a
-- list-free semantic implementation extensionally equal to the existing full
-- Cook quotation codec.  No tableau-wide CNF, Cook AST, token list, or binary
-- formula list is required by `streamedQueryBit` itself.
--
-- Remaining work is representation/complexity compilation to one finite target
-- TM, not the definition of the queried bit.
------------------------------------------------------------------------
