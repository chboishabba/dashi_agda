module DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitCostedExact where

------------------------------------------------------------------------
-- COSTED EXECUTION OF THE ACTUAL TOKEN / THREE-BIT COOK CURSOR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (_×_; _,_)
import Data.Fin.Base as Fin
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseCostExact as ClauseBudget
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseCostedExact as CostedClause
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

record Costed (A : Set) : Set where
  constructor costed
  field
    result : A
    work : Nat

open Costed public

nextTokenCosted :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Cursor.TokenCursorState (Endpoint.ExtendedGlobalWidth machine steps cols) →
  Costed
    (Maybe
      (Prefix.CookSyntaxToken
        × Cursor.TokenCursorState
            (Endpoint.ExtendedGlobalWidth machine steps cols)))
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.cnfAt clauseIndex)
  with CostedClause.globalClauseSeekCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget clauseIndex
... | CostedClause.costed-global-clause (Seek.found clause) clauseWork =
  costed
    (just (Prefix.formulaAndToken , Cursor.clauseAt clauseIndex clause))
    (suc clauseWork)
... | CostedClause.costed-global-clause (Seek.exhausted remaining) clauseWork =
  costed
    (just (Prefix.formulaTrueToken , Cursor.tokenDone))
    (suc clauseWork)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex []) =
  costed (just (Prefix.formulaFalseToken , Cursor.cnfAt (suc clauseIndex))) (suc zero)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex (CNF.positive index ∷ literals)) =
  costed
    (just (Prefix.formulaOrToken , Cursor.positiveVariableAt clauseIndex index literals))
    (suc zero)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex (CNF.negative index ∷ literals)) =
  costed
    (just (Prefix.formulaOrToken , Cursor.negativeVariableAt clauseIndex index literals))
    (suc zero)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.positiveVariableAt clauseIndex index literals) =
  costed
    (just (Prefix.formulaVariableToken , Cursor.natAt clauseIndex (Fin.toℕ index) literals))
    (suc zero)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.negativeVariableAt clauseIndex index literals) =
  costed
    (just (Prefix.formulaNegateToken , Cursor.negativeVariableBodyAt clauseIndex index literals))
    (suc zero)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.negativeVariableBodyAt clauseIndex index literals) =
  costed
    (just (Prefix.formulaVariableToken , Cursor.natAt clauseIndex (Fin.toℕ index) literals))
    (suc zero)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.natAt clauseIndex zero literals) =
  costed (just (Prefix.natZeroToken , Cursor.clauseAt clauseIndex literals)) (suc zero)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.natAt clauseIndex (suc n) literals) =
  costed (just (Prefix.natSuccToken , Cursor.natAt clauseIndex n literals)) (suc zero)
nextTokenCosted stateCoverage symbolCoverage nonempty steps cols initialTarget Cursor.tokenDone =
  costed nothing (suc zero)

nextTokenCostedResultExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.TokenCursorState (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  result (nextTokenCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget state)
  ≡ Cursor.nextToken
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
nextTokenCostedResultExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.cnfAt clauseIndex)
  with CostedClause.globalClauseSeekCosted
      stateCoverage symbolCoverage nonempty steps cols initialTarget clauseIndex
     | CostedClause.globalClauseSeekCostedResultExact
        stateCoverage symbolCoverage nonempty steps cols initialTarget clauseIndex
... | CostedClause.costed-global-clause (Seek.found clause) clauseWork | exact
  rewrite sym exact = refl
... | CostedClause.costed-global-clause (Seek.exhausted remaining) clauseWork | exact
  rewrite sym exact = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex []) = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex (CNF.positive index ∷ literals)) = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex (CNF.negative index ∷ literals)) = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.positiveVariableAt clauseIndex index literals) = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.negativeVariableAt clauseIndex index literals) = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.negativeVariableBodyAt clauseIndex index literals) = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.natAt clauseIndex zero literals) = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.natAt clauseIndex (suc n) literals) = refl
nextTokenCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget Cursor.tokenDone = refl

cursorStepBudget :
  (machine : Local.ConcreteTapeMachine) → Nat → Nat → Nat
cursorStepBudget machine steps cols =
  suc (ClauseBudget.globalClauseSeekWorkBudget machine steps cols)

nextTokenCostedWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.TokenCursorState (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  work (nextTokenCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget state)
  ≤ cursorStepBudget machine steps cols
nextTokenCostedWorkBound {machine}
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.cnfAt clauseIndex)
  with CostedClause.globalClauseSeekCosted
      stateCoverage symbolCoverage nonempty steps cols initialTarget clauseIndex
     | CostedClause.globalClauseSeekCostedWorkBound
        stateCoverage symbolCoverage nonempty steps cols initialTarget clauseIndex
... | CostedClause.costed-global-clause found clauseWork | bound = NatP.s≤s bound
nextTokenCostedWorkBound {machine} stateCoverage symbolCoverage nonempty steps cols initialTarget state =
  NatP.s≤s NatP.z≤n

nextBitCosted :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols) →
  Costed
    (Maybe
      (Bool × Cursor.BitCursorState
        (Endpoint.ExtendedGlobalWidth machine steps cols)))
nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needToken tokenState)
  with nextTokenCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
... | costed nothing tokenWork =
  costed nothing (suc tokenWork)
... | costed (just (token , nextState)) tokenWork =
  costed
    (just (Cursor.firstTokenBit token , Cursor.needSecond token nextState))
    (suc tokenWork)
nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needSecond token nextState) =
  costed
    (just (Cursor.secondTokenBit token , Cursor.needThird token nextState))
    (suc zero)
nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needThird token nextState) =
  costed
    (just (Cursor.thirdTokenBit token , Cursor.needToken nextState))
    (suc zero)
nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget Cursor.bitDone =
  costed nothing (suc zero)

nextBitCostedResultExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  result (nextBitCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget state)
  ≡ Cursor.nextBit
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
nextBitCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needToken tokenState)
  with nextTokenCosted
      stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
     | nextTokenCostedResultExact
        stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
... | costed nothing tokenWork | exact
  rewrite sym exact = refl
... | costed (just (token , nextState)) tokenWork | exact
  rewrite sym exact = refl
nextBitCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needSecond token nextState) = refl
nextBitCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needThird token nextState) = refl
nextBitCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget Cursor.bitDone = refl

bitStepBudget :
  (machine : Local.ConcreteTapeMachine) → Nat → Nat → Nat
bitStepBudget machine steps cols =
  suc (cursorStepBudget machine steps cols)

nextBitCostedWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  work (nextBitCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget state)
  ≤ bitStepBudget machine steps cols
nextBitCostedWorkBound {machine}
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.needToken tokenState)
  with nextTokenCosted
      stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
     | nextTokenCostedWorkBound
        stateCoverage symbolCoverage nonempty steps cols initialTarget tokenState
... | costed tokenResult tokenWork | bound = NatP.s≤s bound
nextBitCostedWorkBound {machine} stateCoverage symbolCoverage nonempty steps cols initialTarget state =
  NatP.s≤s NatP.z≤n

bitAtCosted :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Nat →
  Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols) →
  Costed (Maybe Bool)
bitAtCosted stateCoverage symbolCoverage nonempty steps cols initialTarget zero state
  with nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | costed nothing stepWork = costed nothing stepWork
... | costed (just (bit , nextState)) stepWork = costed (just bit) stepWork
bitAtCosted stateCoverage symbolCoverage nonempty steps cols initialTarget
    (suc index) state
  with nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | costed nothing stepWork = costed nothing stepWork
... | costed (just (bit , nextState)) stepWork
  with bitAtCosted stateCoverage symbolCoverage nonempty steps cols initialTarget index nextState
... | costed found restWork = costed found (stepWork + restWork)

bitAtCostedResultExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat)
    (state : Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  result (bitAtCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget index state)
  ≡ Cursor.bitAtFromState
      stateCoverage symbolCoverage nonempty steps cols initialTarget index state
bitAtCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget zero state
  with nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget state
     | nextBitCostedResultExact
        stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | costed nothing stepWork | exact
  rewrite sym exact = refl
... | costed (just (bit , nextState)) stepWork | exact
  rewrite sym exact = refl
bitAtCostedResultExact stateCoverage symbolCoverage nonempty steps cols initialTarget
    (suc index) state
  with nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget state
     | nextBitCostedResultExact
        stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | costed nothing stepWork | exact
  rewrite sym exact = refl
... | costed (just (bit , nextState)) stepWork | exact
  rewrite sym exact
  with bitAtCosted stateCoverage symbolCoverage nonempty steps cols initialTarget index nextState
     | bitAtCostedResultExact
        stateCoverage symbolCoverage nonempty steps cols initialTarget index nextState
... | costed found restWork | restExact
  rewrite sym restExact = refl

bitAtWorkBudget :
  (machine : Local.ConcreteTapeMachine) → Nat → Nat → Nat → Nat
bitAtWorkBudget machine steps cols index =
  suc index * bitStepBudget machine steps cols

bitAtCostedWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat)
    (state : Cursor.BitCursorState (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  work (bitAtCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget index state)
  ≤ bitAtWorkBudget machine steps cols index
bitAtCostedWorkBound {machine}
    stateCoverage symbolCoverage nonempty steps cols initialTarget zero state =
  nextBitCostedWorkBound
    stateCoverage symbolCoverage nonempty steps cols initialTarget state
bitAtCostedWorkBound {machine}
    stateCoverage symbolCoverage nonempty steps cols initialTarget (suc index) state
  with nextBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget state
     | nextBitCostedWorkBound
        stateCoverage symbolCoverage nonempty steps cols initialTarget state
... | costed nothing stepWork | stepBound =
  NatP.≤-trans
    stepBound
    (NatP.m≤m+n
      (bitStepBudget machine steps cols)
      (suc index * bitStepBudget machine steps cols))
... | costed (just (bit , nextState)) stepWork | stepBound
  with bitAtCosted stateCoverage symbolCoverage nonempty steps cols initialTarget index nextState
     | bitAtCostedWorkBound
        stateCoverage symbolCoverage nonempty steps cols initialTarget index nextState
... | costed found restWork | restBound =
  NatP.+-mono-≤ stepBound restBound

streamedCookBitCosted :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Nat → Costed (Maybe Bool)
streamedCookBitCosted stateCoverage symbolCoverage nonempty steps cols initialTarget index =
  bitAtCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    index
    (Cursor.needToken (Cursor.cnfAt zero))

streamedCookBitCostedResultExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  result (streamedCookBitCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget index)
  ≡ Cursor.streamedCookBit
      stateCoverage symbolCoverage nonempty steps cols initialTarget index
streamedCookBitCostedResultExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget index =
  bitAtCostedResultExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget index
    (Cursor.needToken (Cursor.cnfAt zero))

streamedCookBitCostedWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  work (streamedCookBitCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget index)
  ≤ bitAtWorkBudget machine steps cols index
streamedCookBitCostedWorkBound
    stateCoverage symbolCoverage nonempty steps cols initialTarget index =
  bitAtCostedWorkBound
    stateCoverage symbolCoverage nonempty steps cols initialTarget index
    (Cursor.needToken (Cursor.cnfAt zero))

------------------------------------------------------------------------
-- Returned bit and charged work now come from the SAME streamed recursion.
------------------------------------------------------------------------
