module DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitExact where

------------------------------------------------------------------------
-- BIT-CURSOR BISIMULATION AGAINST THE CANONICAL BINARY COOK CODE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingTokenBisimulationExact as TokenBisim
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Lookup
import DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact as Tokens
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.FixedWidthCNFToCookFormulaExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

------------------------------------------------------------------------
-- The executable bit decomposition is exactly Binary.tokenBits.
------------------------------------------------------------------------

tokenBitsCursorExact :
  (token : Prefix.CookSyntaxToken) →
  Binary.tokenBits token
  ≡
  Cursor.firstTokenBit token
  ∷ Cursor.secondTokenBit token
  ∷ Cursor.thirdTokenBit token
  ∷ []
tokenBitsCursorExact Prefix.natZeroToken = refl
tokenBitsCursorExact Prefix.natSuccToken = refl
tokenBitsCursorExact Prefix.formulaVariableToken = refl
tokenBitsCursorExact Prefix.formulaFalseToken = refl
tokenBitsCursorExact Prefix.formulaTrueToken = refl
tokenBitsCursorExact Prefix.formulaNegateToken = refl
tokenBitsCursorExact Prefix.formulaAndToken = refl
tokenBitsCursorExact Prefix.formulaOrToken = refl

------------------------------------------------------------------------
-- Canonical binary suffix represented by every executable bit cursor state.
------------------------------------------------------------------------

stateBits :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols) →
  List Bool
stateBits stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needToken tokenState) =
  Binary.encodeTokenStream
    (TokenBisim.stateTokens
      stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState)
stateBits stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needSecond token nextState) =
  Cursor.secondTokenBit token
  ∷ Cursor.thirdTokenBit token
  ∷ Binary.encodeTokenStream
      (TokenBisim.stateTokens
        stateCoverage symbolCoverage nonempty steps cols initialTarget nextState)
stateBits stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needThird token nextState) =
  Cursor.thirdTokenBit token
  ∷ Binary.encodeTokenStream
      (TokenBisim.stateTokens
        stateCoverage symbolCoverage nonempty steps cols initialTarget nextState)
stateBits stateCoverage symbolCoverage nonempty steps cols initialTarget
    Cursor.bitDone = []

------------------------------------------------------------------------
-- One bit step is exactly head/tail decomposition of stateBits.
------------------------------------------------------------------------

data BitStateSpec
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.BitCursorState
      (Endpoint.ExtendedGlobalWidth machine steps cols)) : Set where

  specDone :
    Cursor.nextBit
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
    ≡ nothing →
    stateBits
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
    ≡ [] →
    BitStateSpec
      stateCoverage symbolCoverage nonempty steps cols initialTarget state

  specStep :
    ∀ {bit next} →
    Cursor.nextBit
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
    ≡ just (bit , next) →
    stateBits
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
    ≡ bit ∷
      stateBits
        stateCoverage symbolCoverage nonempty steps cols initialTarget next →
    BitStateSpec
      stateCoverage symbolCoverage nonempty steps cols initialTarget state

bitStateSpec :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.BitCursorState
      (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  BitStateSpec
    stateCoverage symbolCoverage nonempty steps cols initialTarget state
bitStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needToken tokenState)
    with TokenBisim.tokenStateSpec
      stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
... | TokenBisim.specDone nextDone tokensDone =
  specDone
    (nextBitDone nextDone)
    (bitsDone tokensDone)
  where
    nextBitDone :
      Cursor.nextToken
        stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
      ≡ nothing →
      Cursor.nextBit
        stateCoverage symbolCoverage nonempty steps cols initialTarget
        (Cursor.needToken tokenState)
      ≡ nothing
    nextBitDone refl = refl

    bitsDone :
      TokenBisim.stateTokens
        stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
      ≡ [] →
      Binary.encodeTokenStream
        (TokenBisim.stateTokens
          stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState)
      ≡ []
    bitsDone refl = refl
... | TokenBisim.specStep {token} {next} tokenStep tokensStep =
  specStep
    (nextBitStep tokenStep)
    (bitsStep tokensStep)
  where
    nextBitStep :
      Cursor.nextToken
        stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
      ≡ just (token , next) →
      Cursor.nextBit
        stateCoverage symbolCoverage nonempty steps cols initialTarget
        (Cursor.needToken tokenState)
      ≡ just
          (Cursor.firstTokenBit token , Cursor.needSecond token next)
    nextBitStep refl = refl

    bitsStep :
      TokenBisim.stateTokens
        stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
      ≡ token ∷
        TokenBisim.stateTokens
          stateCoverage symbolCoverage nonempty steps cols initialTarget next →
      stateBits
        stateCoverage symbolCoverage nonempty steps cols initialTarget
        (Cursor.needToken tokenState)
      ≡ Cursor.firstTokenBit token ∷
          stateBits
            stateCoverage symbolCoverage nonempty steps cols initialTarget
            (Cursor.needSecond token next)
    bitsStep tokensEq
      rewrite tokensEq
            | tokenBitsCursorExact token =
      refl
bitStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needSecond token nextState) =
  specStep refl refl
bitStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needThird token nextState) =
  specStep refl refl
bitStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    Cursor.bitDone =
  specDone refl refl

------------------------------------------------------------------------
-- Index recursion over the executable cursor equals ordinary list lookup.
------------------------------------------------------------------------

bitAtFromStateExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat)
    (state : Cursor.BitCursorState
      (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  Cursor.bitAtFromState
      stateCoverage symbolCoverage nonempty steps cols initialTarget
      index state
  ≡
  Lookup.lookupBit index
    (stateBits
      stateCoverage symbolCoverage nonempty steps cols initialTarget state)
bitAtFromStateExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    zero state
    with bitStateSpec
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | specDone nextDone bitsDone
    rewrite nextDone | bitsDone = refl
... | specStep {bit} {next} nextStep bitsStep
    rewrite nextStep | bitsStep = refl
bitAtFromStateExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (suc index) state
    with bitStateSpec
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | specDone nextDone bitsDone
    rewrite nextDone | bitsDone = refl
... | specStep {bit} {next} nextStep bitsStep
    rewrite nextStep | bitsStep =
  bitAtFromStateExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    index next

------------------------------------------------------------------------
-- Main theorem: streamedCookBit is the canonical binary encoding lookup.
------------------------------------------------------------------------

streamedCookBitExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  Cursor.streamedCookBit
      stateCoverage symbolCoverage nonempty steps cols initialTarget index
  ≡
  Lookup.lookupBit index
    (Binary.encodeFormulaBits
      (Bridge.cnfToCook
        (Global.globalCookLevinCNF
          stateCoverage symbolCoverage nonempty steps cols initialTarget)))
streamedCookBitExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget index =
  transLookup
    (bitAtFromStateExact
      stateCoverage symbolCoverage nonempty steps cols initialTarget
      index (Cursor.needToken (Cursor.cnfAt zero)))
    (Tokens.cnfTokenBitsExact
      (Global.globalCookLevinCNF
        stateCoverage symbolCoverage nonempty steps cols initialTarget))
  where
    transLookup :
      ∀ {left right : List Bool} →
      Cursor.streamedCookBit
          stateCoverage symbolCoverage nonempty steps cols initialTarget index
      ≡ Lookup.lookupBit index left →
      left ≡ right →
      Cursor.streamedCookBit
          stateCoverage symbolCoverage nonempty steps cols initialTarget index
      ≡ Lookup.lookupBit index right
    transLookup proof refl = proof

------------------------------------------------------------------------
-- The semantic indexing wall is paid at this level.  Downstream work may now
-- replace canonical `queryAnswer` by `streamedCookBit` after specializing the
-- guarded initialTarget/cols definitions.  Remaining work is executable finite
-- TM compilation, in-place call-frame simulation, and exact resource closure.
------------------------------------------------------------------------
