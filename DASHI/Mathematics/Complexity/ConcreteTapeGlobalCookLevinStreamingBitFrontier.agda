module DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier where

------------------------------------------------------------------------
-- EXECUTABLE LIST-FREE BIT CURSOR FOR THE ACTUAL GUARDED COOK CONSTRUCTOR
--
-- Correctness of the lower clause selector is already exact.  This owner pays
-- the remaining executable grammar: streamed clauses -> Cook prefix tokens ->
-- fixed three-bit token code.  The final stream-equality theorem to the canonical
-- binary codec is intentionally left explicit at the boundary below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseExact as StreamClause
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix

------------------------------------------------------------------------
-- Prefix-token cursor state.
------------------------------------------------------------------------

data TokenCursorState (width : Nat) : Set where
  cnfAt : Nat → TokenCursorState width
  clauseAt : Nat → CNF.Clause width → TokenCursorState width
  positiveVariableAt :
    Nat → Fin.Fin width → CNF.Clause width → TokenCursorState width
  negativeVariableAt :
    Nat → Fin.Fin width → CNF.Clause width → TokenCursorState width
  negativeVariableBodyAt :
    Nat → Fin.Fin width → CNF.Clause width → TokenCursorState width
  natAt :
    Nat → Nat → CNF.Clause width → TokenCursorState width
  tokenDone : TokenCursorState width

nextToken :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  TokenCursorState (Endpoint.ExtendedGlobalWidth machine steps cols) →
  Maybe
    (Prefix.CookSyntaxToken
      × TokenCursorState (Endpoint.ExtendedGlobalWidth machine steps cols))
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (cnfAt clauseIndex)
    with StreamClause.globalClauseSeek
      stateCoverage symbolCoverage nonempty steps cols initialTarget clauseIndex
... | Seek.found clause =
  just (Prefix.formulaAndToken , clauseAt clauseIndex clause)
... | Seek.exhausted remaining =
  just (Prefix.formulaTrueToken , tokenDone)
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (clauseAt clauseIndex []) =
  just (Prefix.formulaFalseToken , cnfAt (suc clauseIndex))
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (clauseAt clauseIndex (CNF.positive index ∷ literals)) =
  just
    ( Prefix.formulaOrToken
    , positiveVariableAt clauseIndex index literals )
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (clauseAt clauseIndex (CNF.negative index ∷ literals)) =
  just
    ( Prefix.formulaOrToken
    , negativeVariableAt clauseIndex index literals )
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (positiveVariableAt clauseIndex index literals) =
  just
    ( Prefix.formulaVariableToken
    , natAt clauseIndex (Fin.toℕ index) literals )
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (negativeVariableAt clauseIndex index literals) =
  just
    ( Prefix.formulaNegateToken
    , negativeVariableBodyAt clauseIndex index literals )
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (negativeVariableBodyAt clauseIndex index literals) =
  just
    ( Prefix.formulaVariableToken
    , natAt clauseIndex (Fin.toℕ index) literals )
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (natAt clauseIndex zero literals) =
  just (Prefix.natZeroToken , clauseAt clauseIndex literals)
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget
    (natAt clauseIndex (suc n) literals) =
  just (Prefix.natSuccToken , natAt clauseIndex n literals)
nextToken stateCoverage symbolCoverage nonempty steps cols initialTarget tokenDone =
  nothing

------------------------------------------------------------------------
-- Fixed three bits per syntax token.
------------------------------------------------------------------------

firstTokenBit : Prefix.CookSyntaxToken → Bool
firstTokenBit Prefix.natZeroToken = false
firstTokenBit Prefix.natSuccToken = false
firstTokenBit Prefix.formulaVariableToken = false
firstTokenBit Prefix.formulaFalseToken = false
firstTokenBit Prefix.formulaTrueToken = true
firstTokenBit Prefix.formulaNegateToken = true
firstTokenBit Prefix.formulaAndToken = true
firstTokenBit Prefix.formulaOrToken = true

secondTokenBit : Prefix.CookSyntaxToken → Bool
secondTokenBit Prefix.natZeroToken = false
secondTokenBit Prefix.natSuccToken = false
secondTokenBit Prefix.formulaVariableToken = true
secondTokenBit Prefix.formulaFalseToken = true
secondTokenBit Prefix.formulaTrueToken = false
secondTokenBit Prefix.formulaNegateToken = false
secondTokenBit Prefix.formulaAndToken = true
secondTokenBit Prefix.formulaOrToken = true

thirdTokenBit : Prefix.CookSyntaxToken → Bool
thirdTokenBit Prefix.natZeroToken = false
thirdTokenBit Prefix.natSuccToken = true
thirdTokenBit Prefix.formulaVariableToken = false
thirdTokenBit Prefix.formulaFalseToken = true
thirdTokenBit Prefix.formulaTrueToken = false
thirdTokenBit Prefix.formulaNegateToken = true
thirdTokenBit Prefix.formulaAndToken = false
thirdTokenBit Prefix.formulaOrToken = true

------------------------------------------------------------------------
-- Bit cursor.  Every recursive call consumes exactly one requested bit offset.
------------------------------------------------------------------------

data BitCursorState (width : Nat) : Set where
  needToken : TokenCursorState width → BitCursorState width
  needSecond :
    Prefix.CookSyntaxToken → TokenCursorState width → BitCursorState width
  needThird :
    Prefix.CookSyntaxToken → TokenCursorState width → BitCursorState width
  bitDone : BitCursorState width

nextBit :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols) →
  Maybe
    (Bool × BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols))
nextBit stateCoverage symbolCoverage nonempty steps cols initialTarget
    (needToken tokenState)
    with nextToken
      stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
... | nothing = nothing
... | just (token , nextState) =
  just (firstTokenBit token , needSecond token nextState)
nextBit stateCoverage symbolCoverage nonempty steps cols initialTarget
    (needSecond token nextState) =
  just (secondTokenBit token , needThird token nextState)
nextBit stateCoverage symbolCoverage nonempty steps cols initialTarget
    (needThird token nextState) =
  just (thirdTokenBit token , needToken nextState)
nextBit stateCoverage symbolCoverage nonempty steps cols initialTarget bitDone =
  nothing

bitAtFromState :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Nat →
  BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols) →
  Maybe Bool
bitAtFromState stateCoverage symbolCoverage nonempty steps cols initialTarget
    zero state
    with nextBit
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | nothing = nothing
... | just (bit , nextState) = just bit
bitAtFromState stateCoverage symbolCoverage nonempty steps cols initialTarget
    (suc index) state
    with nextBit
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | nothing = nothing
... | just (bit , nextState) =
  bitAtFromState
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    index nextState

streamedCookBit :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Nat → Maybe Bool
streamedCookBit
    stateCoverage symbolCoverage nonempty steps cols initialTarget index =
  bitAtFromState
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    index (needToken (cnfAt zero))

------------------------------------------------------------------------
-- FRONTIER / NO-PROMOTION BOUNDARY
--
-- PAID:
--   * executable list-free global clause selection is exact;
--   * exact Cook prefix grammar for CNF is separately proved in
--     CNFCookPrefixTokenExact;
--   * this owner implements the corresponding token/three-bit cursor.
--
-- STILL REQUIRED BEFORE THIS MAY REPLACE `queryAnswer`:
--   streamedCookBit ... i
--     = lookupBit i (encodeFormulaBits (cnfToCook globalCookLevinCNF ...)).
--
-- That is now a pure stream-bisimulation theorem.  No SAT semantics, fixed-point
-- construction, or tableau-wide materialisation remains inside that theorem.
------------------------------------------------------------------------
