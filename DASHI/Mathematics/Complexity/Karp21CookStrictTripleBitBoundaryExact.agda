module DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact where

------------------------------------------------------------------------
-- K00 REAL STRICT BINARY-FORMULA TOKEN BOUNDARY.
--
-- Reuse the ACTUAL Cook (1971) SAT formula prefix-code syntax owner:
--   PNotEqualsNPCookFormulaPrefixCodecExact
-- and its eight already defined three-bit tokens:
--   PNotEqualsNPCookFormulaBinaryCodecExact.
--
-- The old decodeTokenStream *silently discards* one or two dangling
-- input bits. This strict decoder rejects those invalid byte tails and
-- proves exact encode/decode for ALL token sequences, including the
-- concrete Cook-Levin formula code from Karp21CookLevinConcreteBitWord.
--
-- Remaining: reject complete 3-bit token strings that do not form a
-- valid Cook formula AST. The existing Prefix.decodeCookFormula falls
-- back on malformed tokens; strict syntactic parse remains a separate
-- K00 requirement. Polynomial tape cost also remains unpaid.
--
-- Source: Cook 1971; original DASHI Cook binary/prefix code authors.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook

strictDecodeThreeTokens : List Bool → Maybe (List Prefix.CookSyntaxToken)
strictDecodeThreeTokens [] = just []
strictDecodeThreeTokens (first ∷ []) = nothing
strictDecodeThreeTokens (first ∷ second ∷ []) = nothing
strictDecodeThreeTokens (first ∷ second ∷ third ∷ rest)
  with strictDecodeThreeTokens rest
... | nothing = nothing
... | just tokens =
  just (Binary.decodeTokenBits first second third ∷ tokens)

-- All eight original source-owned token-bit encodings have length 3.
-- No guessed ninth token or separate Karp token list is introduced.
strictDecodeThreeTokensAfterEncode :
  (tokens : List Prefix.CookSyntaxToken) →
  strictDecodeThreeTokens (Binary.encodeTokenStream tokens)
  ≡ just tokens
strictDecodeThreeTokensAfterEncode [] = refl
strictDecodeThreeTokensAfterEncode (token ∷ tokens)
  with token
... | Prefix.natZeroToken
  rewrite strictDecodeThreeTokensAfterEncode tokens = refl
... | Prefix.natSuccToken
  rewrite strictDecodeThreeTokensAfterEncode tokens = refl
... | Prefix.formulaVariableToken
  rewrite strictDecodeThreeTokensAfterEncode tokens = refl
... | Prefix.formulaFalseToken
  rewrite strictDecodeThreeTokensAfterEncode tokens = refl
... | Prefix.formulaTrueToken
  rewrite strictDecodeThreeTokensAfterEncode tokens = refl
... | Prefix.formulaNegateToken
  rewrite strictDecodeThreeTokensAfterEncode tokens = refl
... | Prefix.formulaAndToken
  rewrite strictDecodeThreeTokensAfterEncode tokens = refl
... | Prefix.formulaOrToken
  rewrite strictDecodeThreeTokensAfterEncode tokens = refl

strictCookFormulaTokenRoundTrip :
  (formula : Cook.BooleanFormula) →
  strictDecodeThreeTokens (Binary.encodeFormulaBits formula)
  ≡ just (Prefix.encodeCookFormula formula)
strictCookFormulaTokenRoundTrip formula =
  strictDecodeThreeTokensAfterEncode
    (Prefix.encodeCookFormula formula)

-- Malformed terminal bit-length cannot be silently ignored.
strictRejectOneExtraBit :
  (tokens : List Prefix.CookSyntaxToken)
  (extra : Bool) →
  strictDecodeThreeTokens
    (Binary.append (Binary.encodeTokenStream tokens) (extra ∷ []))
  ≡ nothing
strictRejectOneExtraBit [] extra = refl
strictRejectOneExtraBit (token ∷ tokens) extra
  with token
... | Prefix.natZeroToken
  rewrite strictRejectOneExtraBit tokens extra = refl
... | Prefix.natSuccToken
  rewrite strictRejectOneExtraBit tokens extra = refl
... | Prefix.formulaVariableToken
  rewrite strictRejectOneExtraBit tokens extra = refl
... | Prefix.formulaFalseToken
  rewrite strictRejectOneExtraBit tokens extra = refl
... | Prefix.formulaTrueToken
  rewrite strictRejectOneExtraBit tokens extra = refl
... | Prefix.formulaNegateToken
  rewrite strictRejectOneExtraBit tokens extra = refl
... | Prefix.formulaAndToken
  rewrite strictRejectOneExtraBit tokens extra = refl
... | Prefix.formulaOrToken
  rewrite strictRejectOneExtraBit tokens extra = refl

strictRejectTwoExtraBits :
  (tokens : List Prefix.CookSyntaxToken)
  (first second : Bool) →
  strictDecodeThreeTokens
    (Binary.append (Binary.encodeTokenStream tokens)
      (first ∷ second ∷ []))
  ≡ nothing
strictRejectTwoExtraBits [] first second = refl
strictRejectTwoExtraBits (token ∷ tokens) first second
  with token
... | Prefix.natZeroToken
  rewrite strictRejectTwoExtraBits tokens first second = refl
... | Prefix.natSuccToken
  rewrite strictRejectTwoExtraBits tokens first second = refl
... | Prefix.formulaVariableToken
  rewrite strictRejectTwoExtraBits tokens first second = refl
... | Prefix.formulaFalseToken
  rewrite strictRejectTwoExtraBits tokens first second = refl
... | Prefix.formulaTrueToken
  rewrite strictRejectTwoExtraBits tokens first second = refl
... | Prefix.formulaNegateToken
  rewrite strictRejectTwoExtraBits tokens first second = refl
... | Prefix.formulaAndToken
  rewrite strictRejectTwoExtraBits tokens first second = refl
... | Prefix.formulaOrToken
  rewrite strictRejectTwoExtraBits tokens first second = refl


------------------------------------------------------------------------
-- Genuine AST-level STRICT parser using the repository's already
-- source-written suffix-preserving Cook prefix grammar.
--
-- Before this pass, decoding could silently discard dangling bits and
-- the older decodeCookFormula also selected a default formula when
-- parsing failed. The strict boundary instead returns nothing for:
--   * incomplete 3-bit tokens,
--   * token streams that are not a formula,
--   * a complete formula followed by ANY unconsumed token(s).
------------------------------------------------------------------------

strictDecodeCookFormulaBits :
  List Bool → Maybe Cook.BooleanFormula
strictDecodeCookFormulaBits word
  with strictDecodeThreeTokens word
... | nothing = nothing
... | just tokens with Prefix.parseCookFormula tokens
...   | Prefix.parseFailure = nothing
...   | Prefix.parsed formula [] = just formula
...   | Prefix.parsed formula (_ ∷ _) = nothing

strictCookFormulaRoundTrip :
  (formula : Cook.BooleanFormula) →
  strictDecodeCookFormulaBits (Binary.encodeFormulaBits formula)
  ≡ just formula
strictCookFormulaRoundTrip formula
  rewrite strictCookFormulaTokenRoundTrip formula
        | Prefix.parseEncodedCookFormula formula = refl

-- Even three COMPLETE extra bits forming a valid additional formula
-- token are rejected, rather than ignored by a prefix decoder.
strictRejectTrailingCompleteFormulaToken :
  (formula : Cook.BooleanFormula) →
  strictDecodeCookFormulaBits
    (Binary.encodeTokenStream
      (Prefix.encodeCookFormulaInto formula
        (Prefix.formulaFalseToken ∷ [])))
  ≡ nothing
strictRejectTrailingCompleteFormulaToken formula
  rewrite strictDecodeThreeTokensAfterEncode
    (Prefix.encodeCookFormulaInto formula
      (Prefix.formulaFalseToken ∷ []))
        | Prefix.parseCookFormulaEncodeInto formula
            (Prefix.formulaFalseToken ∷ []) = refl

-- A standalone token used only for integer encoding is never a
-- complete top-level Boolean formula.
strictRejectStandaloneNatZero :
  strictDecodeCookFormulaBits
    (Binary.tokenBits Prefix.natZeroToken) ≡ nothing
strictRejectStandaloneNatZero = refl
