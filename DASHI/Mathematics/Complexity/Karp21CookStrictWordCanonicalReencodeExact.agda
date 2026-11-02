{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21CookStrictWordCanonicalReencodeExact where

------------------------------------------------------------------------
-- K00 FIRST PRIORITY: ALL ACCEPTED STRICT COOK WORDS ARE CANONICAL.
--
-- A prior right-inverse decode(encode(formula)) = formula is NOT enough
-- to bound certificates on arbitrary accepted words. This module
-- proves the converse on the successful strict parser domain:
--
--   strictDecodeCookFormulaBits word = just formula
--        => encodeFormulaBits formula = word.
--
-- Both the unary Nat prefix parser and recursive formula parser are
-- checked on their original source-owned grammars. We also reconstruct
-- each exact 3-bit token word. Thus the existing finite Cook certificate
-- bound applies to EVERY accepted strict SAT input, not only words
-- directly produced by our encoder.
--
-- Reuse Cook (1971), Leonid Levin (1973) search, DASHI Prefix,
-- Binary, Strict and executable Cook verifier owners.
-- Separate: machine clock, NP-completeness and Agda kernel acceptance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict
import DASHI.Mathematics.Complexity.Karp21CookExecutableFiniteVerifierBidiExact as Verifier
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21SparseEndpointConsistencySoundExact as N21

failureIsNotParsed :
  ∀ {A : Set} {value : A} {rest : List Prefix.CookSyntaxToken} →
  Prefix.parseFailure ≡ Prefix.parsed value rest → ⊥
failureIsNotParsed ()

nothingIsNotJust :
  ∀ {A : Set} {value : A} →
  nothing ≡ just value → ⊥
nothingIsNotJust ()

------------------------------------------------------------------------
-- Inverse to the SAME suffix-preserving unary natural-number parser.
-- Proof is by recursion on the input token list, not on max index.
------------------------------------------------------------------------

NatReencoded :
  (tokens : List Prefix.CookSyntaxToken) →
  Prefix.ParseResult Nat → Set
NatReencoded tokens Prefix.parseFailure = ⊤
NatReencoded tokens (Prefix.parsed n suffix) =
  tokens ≡ Prefix.encodeNatInto n suffix

natRebuildOutcome :
  (tokens : List Prefix.CookSyntaxToken) →
  NatReencoded tokens (Prefix.parseNat tokens)
natRebuildOutcome [] = tt
natRebuildOutcome (Prefix.natZeroToken ∷ rest) = refl
natRebuildOutcome (Prefix.natSuccToken ∷ rest)
  with Prefix.parseNat rest | natRebuildOutcome rest
... | Prefix.parseFailure | _ = tt
... | Prefix.parsed n suffix | proof =
  cong (Prefix.natSuccToken ∷_) proof
natRebuildOutcome (Prefix.formulaVariableToken ∷ rest) = tt
natRebuildOutcome (Prefix.formulaFalseToken ∷ rest) = tt
natRebuildOutcome (Prefix.formulaTrueToken ∷ rest) = tt
natRebuildOutcome (Prefix.formulaNegateToken ∷ rest) = tt
natRebuildOutcome (Prefix.formulaAndToken ∷ rest) = tt
natRebuildOutcome (Prefix.formulaOrToken ∷ rest) = tt

natSuccessCanonical :
  (tokens : List Prefix.CookSyntaxToken)
  (n : Nat) (suffix : List Prefix.CookSyntaxToken) →
  Prefix.parseNat tokens ≡ Prefix.parsed n suffix →
  tokens ≡ Prefix.encodeNatInto n suffix
natSuccessCanonical tokens n suffix evidence =
  subst (NatReencoded tokens) evidence (natRebuildOutcome tokens)

------------------------------------------------------------------------

------------------------------------------------------------------------
-- Explicit first-token soundness of the original prefix parser.
-- We need this to reject *all* constructor mismatches, including
-- branches whose child parse results are not definitionally known.
------------------------------------------------------------------------

data FormulaTop : Set where
  topVariable topFalse topTrue topNegate topConjunction topDisjunction
    topInvalid : FormulaTop

formulaTop : Cook.BooleanFormula → FormulaTop
formulaTop (Cook.variable _) = topVariable
formulaTop (Cook.constant false) = topFalse
formulaTop (Cook.constant true) = topTrue
formulaTop (Cook.negate _) = topNegate
formulaTop (Cook.conjunction _ _) = topConjunction
formulaTop (Cook.disjunction _ _) = topDisjunction

tokenTop : Prefix.CookSyntaxToken → FormulaTop
tokenTop Prefix.natZeroToken = topInvalid
tokenTop Prefix.natSuccToken = topInvalid
tokenTop Prefix.formulaVariableToken = topVariable
tokenTop Prefix.formulaFalseToken = topFalse
tokenTop Prefix.formulaTrueToken = topTrue
tokenTop Prefix.formulaNegateToken = topNegate
tokenTop Prefix.formulaAndToken = topConjunction
tokenTop Prefix.formulaOrToken = topDisjunction

parsedFormulaTopMatchesInput :
  (token : Prefix.CookSyntaxToken)
  (rest : List Prefix.CookSyntaxToken)
  (formula : Cook.BooleanFormula)
  (suffix : List Prefix.CookSyntaxToken) →
  Prefix.parseCookFormula (token ∷ rest) ≡
    Prefix.parsed formula suffix →
  formulaTop formula ≡ tokenTop token
parsedFormulaTopMatchesInput Prefix.natZeroToken rest formula suffix eq =
  ⊥-elim (failureIsNotParsed eq)
parsedFormulaTopMatchesInput Prefix.natSuccToken rest formula suffix eq =
  ⊥-elim (failureIsNotParsed eq)
parsedFormulaTopMatchesInput
  Prefix.formulaFalseToken rest .(Cook.constant false) .rest refl = refl
parsedFormulaTopMatchesInput
  Prefix.formulaTrueToken rest .(Cook.constant true) .rest refl = refl
parsedFormulaTopMatchesInput
  Prefix.formulaVariableToken rest formula suffix eq
  with Prefix.parseNat rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
... | Prefix.parsed n afterNat with eq
...   | refl = refl
parsedFormulaTopMatchesInput
  Prefix.formulaNegateToken rest formula suffix eq
  with Prefix.parseCookFormula rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
... | Prefix.parsed child afterChild with eq
...   | refl = refl
parsedFormulaTopMatchesInput
  Prefix.formulaAndToken rest formula suffix eq
  with Prefix.parseCookFormula rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
... | Prefix.parsed left afterLeft
  with Prefix.parseCookFormula afterLeft
...   | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
...   | Prefix.parsed right afterRight with eq
...     | refl = refl
parsedFormulaTopMatchesInput
  Prefix.formulaOrToken rest formula suffix eq
  with Prefix.parseCookFormula rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
... | Prefix.parsed left afterLeft
  with Prefix.parseCookFormula afterLeft
...   | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
...   | Prefix.parsed right afterRight with eq
...     | refl = refl

-- Strong parser inverse: structural recursion is on the decoded
-- BooleanFormula, so both subformula calls in an AND/OR are smaller.
-- The second parse may consume a suffix discovered by the first.
------------------------------------------------------------------------

rebuildCook :
  (formula : Cook.BooleanFormula)
  (tokens suffix : List Prefix.CookSyntaxToken) →
  Prefix.parseCookFormula tokens ≡ Prefix.parsed formula suffix →
  tokens ≡ Prefix.encodeCookFormulaInto formula suffix
rebuildCook (Cook.variable index) [] suffix ()
rebuildCook (Cook.variable index) (Prefix.natZeroToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natZeroToken rest (Cook.variable index) suffix evidence))
rebuildCook (Cook.variable index) (Prefix.natSuccToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natSuccToken rest (Cook.variable index) suffix evidence))
rebuildCook (Cook.variable index) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaFalseToken rest (Cook.variable index) suffix evidence))
rebuildCook (Cook.variable index) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaTrueToken rest (Cook.variable index) suffix evidence))
rebuildCook (Cook.variable index) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaNegateToken rest (Cook.variable index) suffix evidence))
rebuildCook (Cook.variable index) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaAndToken rest (Cook.variable index) suffix evidence))
rebuildCook (Cook.variable index) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaOrToken rest (Cook.variable index) suffix evidence))
rebuildCook (Cook.variable index)
  (Prefix.formulaVariableToken ∷ rest) suffix evidence
  with Prefix.parseNat rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
... | Prefix.parsed parsedIndex parsedSuffix with evidence
...   | refl =
  cong (Prefix.formulaVariableToken ∷_)
    (natSuccessCanonical rest index suffix refl)

rebuildCook (Cook.constant false) [] suffix ()
rebuildCook (Cook.constant false) (Prefix.natZeroToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natZeroToken rest (Cook.constant false) suffix evidence))
rebuildCook (Cook.constant false) (Prefix.natSuccToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natSuccToken rest (Cook.constant false) suffix evidence))
rebuildCook (Cook.constant false) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaVariableToken rest (Cook.constant false) suffix evidence))
rebuildCook (Cook.constant false) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaTrueToken rest (Cook.constant false) suffix evidence))
rebuildCook (Cook.constant false) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaNegateToken rest (Cook.constant false) suffix evidence))
rebuildCook (Cook.constant false) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaAndToken rest (Cook.constant false) suffix evidence))
rebuildCook (Cook.constant false) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaOrToken rest (Cook.constant false) suffix evidence))
rebuildCook (Cook.constant false)
  (Prefix.formulaFalseToken ∷ rest) .rest refl = refl

rebuildCook (Cook.constant true) [] suffix ()
rebuildCook (Cook.constant true) (Prefix.natZeroToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natZeroToken rest (Cook.constant true) suffix evidence))
rebuildCook (Cook.constant true) (Prefix.natSuccToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natSuccToken rest (Cook.constant true) suffix evidence))
rebuildCook (Cook.constant true) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaVariableToken rest (Cook.constant true) suffix evidence))
rebuildCook (Cook.constant true) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaFalseToken rest (Cook.constant true) suffix evidence))
rebuildCook (Cook.constant true) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaNegateToken rest (Cook.constant true) suffix evidence))
rebuildCook (Cook.constant true) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaAndToken rest (Cook.constant true) suffix evidence))
rebuildCook (Cook.constant true) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaOrToken rest (Cook.constant true) suffix evidence))
rebuildCook (Cook.constant true)
  (Prefix.formulaTrueToken ∷ rest) .rest refl = refl

rebuildCook (Cook.negate child) [] suffix ()
rebuildCook (Cook.negate child) (Prefix.natZeroToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natZeroToken rest (Cook.negate child) suffix evidence))
rebuildCook (Cook.negate child) (Prefix.natSuccToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natSuccToken rest (Cook.negate child) suffix evidence))
rebuildCook (Cook.negate child) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaVariableToken rest (Cook.negate child) suffix evidence))
rebuildCook (Cook.negate child) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaFalseToken rest (Cook.negate child) suffix evidence))
rebuildCook (Cook.negate child) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaTrueToken rest (Cook.negate child) suffix evidence))
rebuildCook (Cook.negate child) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaAndToken rest (Cook.negate child) suffix evidence))
rebuildCook (Cook.negate child) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaOrToken rest (Cook.negate child) suffix evidence))
rebuildCook (Cook.negate child)
  (Prefix.formulaNegateToken ∷ rest) suffix evidence
  with Prefix.parseCookFormula rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
... | Prefix.parsed parsedChild parsedSuffix with evidence
...   | refl =
  cong (Prefix.formulaNegateToken ∷_)
    (rebuildCook child rest suffix refl)

rebuildCook (Cook.conjunction left right) [] suffix ()
rebuildCook (Cook.conjunction left right) (Prefix.natZeroToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natZeroToken rest (Cook.conjunction left right) suffix evidence))
rebuildCook (Cook.conjunction left right) (Prefix.natSuccToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natSuccToken rest (Cook.conjunction left right) suffix evidence))
rebuildCook (Cook.conjunction left right) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaVariableToken rest (Cook.conjunction left right) suffix evidence))
rebuildCook (Cook.conjunction left right) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaFalseToken rest (Cook.conjunction left right) suffix evidence))
rebuildCook (Cook.conjunction left right) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaTrueToken rest (Cook.conjunction left right) suffix evidence))
rebuildCook (Cook.conjunction left right) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaNegateToken rest (Cook.conjunction left right) suffix evidence))
rebuildCook (Cook.conjunction left right) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaOrToken rest (Cook.conjunction left right) suffix evidence))
rebuildCook (Cook.conjunction left right)
  (Prefix.formulaAndToken ∷ rest) suffix evidence
  with Prefix.parseCookFormula rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
... | Prefix.parsed parsedLeft afterLeft
  with Prefix.parseCookFormula afterLeft
...   | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
...   | Prefix.parsed parsedRight afterRight with evidence
...     | refl =
  cong (Prefix.formulaAndToken ∷_)
    (trans
      (rebuildCook left rest afterLeft refl)
      (cong (Prefix.encodeCookFormulaInto left)
        (rebuildCook right afterLeft suffix refl)))

rebuildCook (Cook.disjunction left right) [] suffix ()
rebuildCook (Cook.disjunction left right) (Prefix.natZeroToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natZeroToken rest (Cook.disjunction left right) suffix evidence))
rebuildCook (Cook.disjunction left right) (Prefix.natSuccToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.natSuccToken rest (Cook.disjunction left right) suffix evidence))
rebuildCook (Cook.disjunction left right) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaVariableToken rest (Cook.disjunction left right) suffix evidence))
rebuildCook (Cook.disjunction left right) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaFalseToken rest (Cook.disjunction left right) suffix evidence))
rebuildCook (Cook.disjunction left right) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaTrueToken rest (Cook.disjunction left right) suffix evidence))
rebuildCook (Cook.disjunction left right) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaNegateToken rest (Cook.disjunction left right) suffix evidence))
rebuildCook (Cook.disjunction left right) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  ⊥-elim ((λ ())
    (parsedFormulaTopMatchesInput
      Prefix.formulaAndToken rest (Cook.disjunction left right) suffix evidence))
rebuildCook (Cook.disjunction left right)
  (Prefix.formulaOrToken ∷ rest) suffix evidence
  with Prefix.parseCookFormula rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
... | Prefix.parsed parsedLeft afterLeft
  with Prefix.parseCookFormula afterLeft
...   | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
...   | Prefix.parsed parsedRight afterRight with evidence
...     | refl =
  cong (Prefix.formulaOrToken ∷_)
    (trans
      (rebuildCook left rest afterLeft refl)
      (cong (Prefix.encodeCookFormulaInto left)
        (rebuildCook right afterLeft suffix refl)))


------------------------------------------------------------------------
-- 3-bit token serializer is inverse to the strict decoder on success.
------------------------------------------------------------------------

bitsAfterDecode :
  (a b c : Bool) →
  Binary.tokenBits (Binary.decodeTokenBits a b c)
    ≡ a ∷ b ∷ c ∷ []
bitsAfterDecode false false false = refl
bitsAfterDecode false false true = refl
bitsAfterDecode false true false = refl
bitsAfterDecode false true true = refl
bitsAfterDecode true false false = refl
bitsAfterDecode true false true = refl
bitsAfterDecode true true false = refl
bitsAfterDecode true true true = refl

reencodeThreeTokens :
  (word : List Bool) (tokens : List Prefix.CookSyntaxToken) →
  Strict.strictDecodeThreeTokens word ≡ just tokens →
  Binary.encodeTokenStream tokens ≡ word
reencodeThreeTokens [] [] refl = refl
reencodeThreeTokens [] (_ ∷ _) ()
reencodeThreeTokens (a ∷ []) tokens ()
reencodeThreeTokens (a ∷ b ∷ []) tokens ()
reencodeThreeTokens (a ∷ b ∷ c ∷ rest) tokens evidence
  with Strict.strictDecodeThreeTokens rest
... | nothing = ⊥-elim (nothingIsNotJust evidence)
... | just tailTokens with evidence
...   | refl
  rewrite bitsAfterDecode a b c
        | reencodeThreeTokens rest tailTokens refl =
  refl

------------------------------------------------------------------------
-- P0 exact original lemma: all accepted words replay to themselves.
-- No alternative canonical SAT language is introduced.
------------------------------------------------------------------------

k00StrictAcceptedWordCanonicalReencode :
  (word : Word.BitWord) (formula : Cook.BooleanFormula) →
  Strict.strictDecodeCookFormulaBits word ≡ just formula →
  Binary.encodeFormulaBits formula ≡ word
k00StrictAcceptedWordCanonicalReencode word formula evidence
  with Strict.strictDecodeThreeTokens word
... | nothing = ⊥-elim (nothingIsNotJust evidence)
... | just tokens with Prefix.parseCookFormula tokens
...   | Prefix.parseFailure = ⊥-elim (nothingIsNotJust evidence)
...   | Prefix.parsed p (_ ∷ rest) =
  ⊥-elim (nothingIsNotJust evidence)
...   | Prefix.parsed p [] with evidence
...     | refl =
  trans
    (cong Binary.encodeTokenStream
      (sym (rebuildCook p tokens [] refl)))
    (reencodeThreeTokens word tokens refl)

-- Exact linear certificate-size bound in the ACTUAL input bit count
-- for every accepted verifier input, not only canonical sample words.
k00StrictAcceptedWordCertificateBound :
  (word bits : Word.BitWord) →
  Verifier.verifyStrictCookSATWord word bits ≡ true →
  Word.encodingSize bits ≤ Word.encodingSize word
k00StrictAcceptedWordCertificateBound word bits verified
  with Strict.strictDecodeCookFormulaBits word
... | nothing = ⊥-elim (N21.falseNotTrue verified)
... | just formula =
  subst
    (λ actualWord →
      Word.encodingSize bits ≤ Word.encodingSize actualWord)
    (k00StrictAcceptedWordCanonicalReencode word formula refl)
    (Verifier.cookExecutableCertificateCanonicalSize
      formula bits verified)
