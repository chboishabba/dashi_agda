module DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingTokenBisimulationExact where

------------------------------------------------------------------------
-- TOKEN-CURSOR BISIMULATION AGAINST THE CANONICAL CNF -> COOK PREFIX STREAM
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseExact as StreamClause
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek
import DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact as Tokens
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix

drop : ∀ {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (x ∷ xs) = drop n xs

seekFoundDrop :
  ∀ {A : Set}
    (index : Nat)
    (xs : List A)
    (x : A) →
  Seek.seekList index xs ≡ Seek.found x →
  drop index xs ≡ x ∷ drop (suc index) xs
seekFoundDrop zero [] x ()
seekFoundDrop zero (y ∷ ys) x refl = refl
seekFoundDrop (suc index) [] x ()
seekFoundDrop (suc index) (y ∷ ys) x proof =
  seekFoundDrop index ys x proof

seekExhaustedDrop :
  ∀ {A : Set}
    (index remaining : Nat)
    (xs : List A) →
  Seek.seekList index xs ≡ Seek.exhausted remaining →
  drop index xs ≡ []
seekExhaustedDrop zero [] remaining refl = refl
seekExhaustedDrop zero (x ∷ xs) remaining ()
seekExhaustedDrop (suc index) [] remaining refl = refl
seekExhaustedDrop (suc index) (x ∷ xs) remaining proof =
  seekExhaustedDrop index remaining xs proof

globalFormula :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps cols)
globalFormula = Global.globalCookLevinCNF

stateTokens :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Cursor.TokenCursorState (Endpoint.ExtendedGlobalWidth machine steps cols) →
  List Prefix.CookSyntaxToken
stateTokens stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.cnfAt clauseIndex) =
  Tokens.cnfTokens
    (drop clauseIndex
      (globalFormula
        stateCoverage symbolCoverage nonempty steps cols initialTarget))
stateTokens stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex clause) =
  Tokens.clauseTokensInto clause
    (Tokens.cnfTokens
      (drop (suc clauseIndex)
        (globalFormula
          stateCoverage symbolCoverage nonempty steps cols initialTarget)))
stateTokens stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.positiveVariableAt clauseIndex index literals) =
  Tokens.literalTokensInto (CNF.positive index)
    (Tokens.clauseTokensInto literals
      (Tokens.cnfTokens
        (drop (suc clauseIndex)
          (globalFormula
            stateCoverage symbolCoverage nonempty steps cols initialTarget))))
stateTokens stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.negativeVariableAt clauseIndex index literals) =
  Tokens.literalTokensInto (CNF.negative index)
    (Tokens.clauseTokensInto literals
      (Tokens.cnfTokens
        (drop (suc clauseIndex)
          (globalFormula
            stateCoverage symbolCoverage nonempty steps cols initialTarget))))
stateTokens stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.negativeVariableBodyAt clauseIndex index literals) =
  Prefix.formulaVariableToken
  ∷ Prefix.encodeNatInto (Fin.toℕ index)
      (Tokens.clauseTokensInto literals
        (Tokens.cnfTokens
          (drop (suc clauseIndex)
            (globalFormula
              stateCoverage symbolCoverage nonempty steps cols initialTarget))))
stateTokens stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.natAt clauseIndex n literals) =
  Prefix.encodeNatInto n
    (Tokens.clauseTokensInto literals
      (Tokens.cnfTokens
        (drop (suc clauseIndex)
          (globalFormula
            stateCoverage symbolCoverage nonempty steps cols initialTarget))))
stateTokens stateCoverage symbolCoverage nonempty steps cols initialTarget
    Cursor.tokenDone = []

data TokenStateSpec
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.TokenCursorState
      (Endpoint.ExtendedGlobalWidth machine steps cols)) : Set where
  specDone :
    Cursor.nextToken
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
    ≡ nothing →
    stateTokens
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
    ≡ [] →
    TokenStateSpec
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
  specStep :
    ∀ {token next} →
    Cursor.nextToken
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
    ≡ just (token , next) →
    stateTokens
      stateCoverage symbolCoverage nonempty steps cols initialTarget state
    ≡ token ∷
      stateTokens
        stateCoverage symbolCoverage nonempty steps cols initialTarget next →
    TokenStateSpec
      stateCoverage symbolCoverage nonempty steps cols initialTarget state

tokenStateSpec :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (state : Cursor.TokenCursorState
      (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  TokenStateSpec
    stateCoverage symbolCoverage nonempty steps cols initialTarget state
tokenStateSpec
    stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.cnfAt clauseIndex)
    with StreamClause.globalClauseSeek
      stateCoverage symbolCoverage nonempty steps cols initialTarget clauseIndex
       | StreamClause.globalClauseSeekExact
          stateCoverage symbolCoverage nonempty steps cols initialTarget clauseIndex
... | Seek.found clause | exact =
  specStep refl
    (tokensFound
      (seekFoundDrop clauseIndex formula clause (sym exact)))
  where
    formula =
      globalFormula stateCoverage symbolCoverage nonempty steps cols initialTarget
    tokensFound :
      drop clauseIndex formula ≡ clause ∷ drop (suc clauseIndex) formula →
      Tokens.cnfTokens (drop clauseIndex formula)
      ≡ Prefix.formulaAndToken ∷
          Tokens.clauseTokensInto clause
            (Tokens.cnfTokens (drop (suc clauseIndex) formula))
    tokensFound refl = refl
... | Seek.exhausted remaining | exact =
  specStep refl
    (tokensExhausted
      (seekExhaustedDrop clauseIndex remaining formula (sym exact)))
  where
    formula =
      globalFormula stateCoverage symbolCoverage nonempty steps cols initialTarget
    tokensExhausted :
      drop clauseIndex formula ≡ [] →
      Tokens.cnfTokens (drop clauseIndex formula)
      ≡ Prefix.formulaTrueToken ∷ []
    tokensExhausted refl = refl

tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex []) = specStep refl refl
tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex (CNF.positive index ∷ literals)) = specStep refl refl
tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.clauseAt clauseIndex (CNF.negative index ∷ literals)) = specStep refl refl
tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.positiveVariableAt clauseIndex index literals) = specStep refl refl
tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.negativeVariableAt clauseIndex index literals) = specStep refl refl
tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.negativeVariableBodyAt clauseIndex index literals) = specStep refl refl
tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.natAt clauseIndex zero literals) = specStep refl refl
tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.natAt clauseIndex (suc n) literals) = specStep refl refl
tokenStateSpec stateCoverage symbolCoverage nonempty steps cols initialTarget
    Cursor.tokenDone = specDone refl refl

initialStateTokensExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  stateTokens stateCoverage symbolCoverage nonempty steps cols initialTarget
    (Cursor.cnfAt zero)
  ≡
  Tokens.cnfTokens
    (Global.globalCookLevinCNF
      stateCoverage symbolCoverage nonempty steps cols initialTarget)
initialStateTokensExact stateCoverage symbolCoverage nonempty steps cols initialTarget = refl
