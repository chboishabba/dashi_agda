module DASHI.Mathematics.Complexity.GuardedCookStreamingBitExact where

------------------------------------------------------------------------
-- CANONICAL GUARDED COOK QUERY = LIST-FREE STREAMED BIT CURSOR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitExact as Exact

streamedQueryBit :
  Query.GuardedCookBitQuery → Maybe Bool
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
