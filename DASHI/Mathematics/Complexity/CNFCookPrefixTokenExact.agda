module DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact where

------------------------------------------------------------------------
-- DIRECT CNF -> COOK PREFIX TOKENS, EXACTLY THE EXISTING COMPOSED COMPILER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.FixedWidthCNFToCookFormulaExact as Bridge

literalTokensInto :
  ∀ {width} →
  CNF.Literal width →
  List Prefix.CookSyntaxToken →
  List Prefix.CookSyntaxToken
literalTokensInto (CNF.positive index) rest =
  Prefix.formulaVariableToken
  ∷ Prefix.encodeNatInto (Fin.toℕ index) rest
literalTokensInto (CNF.negative index) rest =
  Prefix.formulaNegateToken
  ∷ Prefix.formulaVariableToken
  ∷ Prefix.encodeNatInto (Fin.toℕ index) rest

clauseTokensInto :
  ∀ {width} →
  CNF.Clause width →
  List Prefix.CookSyntaxToken →
  List Prefix.CookSyntaxToken
clauseTokensInto [] rest =
  Prefix.formulaFalseToken ∷ rest
clauseTokensInto (literal ∷ literals) rest =
  Prefix.formulaOrToken
  ∷ literalTokensInto literal
    (clauseTokensInto literals rest)

cnfTokensInto :
  ∀ {width} →
  CNF.CNF width →
  List Prefix.CookSyntaxToken →
  List Prefix.CookSyntaxToken
cnfTokensInto [] rest =
  Prefix.formulaTrueToken ∷ rest
cnfTokensInto (clause ∷ clauses) rest =
  Prefix.formulaAndToken
  ∷ clauseTokensInto clause
    (cnfTokensInto clauses rest)

literalTokensIntoExact :
  ∀ {width}
    (literal : CNF.Literal width)
    (rest : List Prefix.CookSyntaxToken) →
  literalTokensInto literal rest
  ≡ Prefix.encodeCookFormulaInto
      (Bridge.literalToCook literal) rest
literalTokensIntoExact (CNF.positive index) rest = refl
literalTokensIntoExact (CNF.negative index) rest = refl

clauseTokensIntoExact :
  ∀ {width}
    (clause : CNF.Clause width)
    (rest : List Prefix.CookSyntaxToken) →
  clauseTokensInto clause rest
  ≡ Prefix.encodeCookFormulaInto
      (Bridge.clauseToCook clause) rest
clauseTokensIntoExact [] rest = refl
clauseTokensIntoExact (literal ∷ literals) rest
  rewrite literalTokensIntoExact literal (clauseTokensInto literals rest)
        | clauseTokensIntoExact literals rest =
  refl

cnfTokensIntoExact :
  ∀ {width}
    (formula : CNF.CNF width)
    (rest : List Prefix.CookSyntaxToken) →
  cnfTokensInto formula rest
  ≡ Prefix.encodeCookFormulaInto
      (Bridge.cnfToCook formula) rest
cnfTokensIntoExact [] rest = refl
cnfTokensIntoExact (clause ∷ clauses) rest
  rewrite clauseTokensIntoExact clause (cnfTokensInto clauses rest)
        | cnfTokensIntoExact clauses rest =
  refl

cnfTokens :
  ∀ {width} →
  CNF.CNF width →
  List Prefix.CookSyntaxToken
cnfTokens formula = cnfTokensInto formula []

cnfTokensExact :
  ∀ {width}
    (formula : CNF.CNF width) →
  cnfTokens formula
  ≡ Prefix.encodeCookFormula (Bridge.cnfToCook formula)
cnfTokensExact formula = cnfTokensIntoExact formula []

cnfTokenBits :
  ∀ {width} →
  CNF.CNF width →
  List Bool
cnfTokenBits formula = Binary.encodeTokenStream (cnfTokens formula)

cnfTokenBitsExact :
  ∀ {width}
    (formula : CNF.CNF width) →
  cnfTokenBits formula
  ≡ Binary.encodeFormulaBits (Bridge.cnfToCook formula)
cnfTokenBitsExact formula
  rewrite cnfTokensExact formula = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The guarded Cook quotation may be queried at the much simpler prefix-token
-- grammar generated directly from CNF structure.  This theorem is exact against
-- the repository's existing `cnfToCook` and binary formula codec; no alternate
-- SAT representation is introduced.
------------------------------------------------------------------------
