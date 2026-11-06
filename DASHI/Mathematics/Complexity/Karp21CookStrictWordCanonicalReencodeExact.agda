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
-- Both unary Nat and recursive formula parsers use original source-owned
-- grammar. The certificate bound is intentionally OUTSIDE this Golden
-- parser inverse module, in Karp21CookAllWordCertificateBoundExact.
--
-- Reuse Cook (1971), Leonid Levin (1973) search, DASHI Prefix,
-- Binary, Strict and executable Cook verifier owners.
-- Separate: machine clock, NP-completeness and Agda kernel acceptance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

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
formulaTop (Cook.formulaVar _) = topVariable
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

topNeq : FormulaTop → FormulaTop → Set
topNeq topVariable topVariable = ⊥
topNeq topFalse topFalse = ⊥
topNeq topTrue topTrue = ⊥
topNeq topNegate topNegate = ⊥
topNeq topConjunction topConjunction = ⊥
topNeq topDisjunction topDisjunction = ⊥
topNeq topInvalid topInvalid = ⊥
topNeq _ _ = ⊤

noTopMatch : ∀ {A : Set} {a b : FormulaTop} → a ≡ b → topNeq a b → A
noTopMatch {a = topVariable} {b = topVariable} refl ()
noTopMatch {a = topFalse} {b = topFalse} refl ()
noTopMatch {a = topTrue} {b = topTrue} refl ()
noTopMatch {a = topNegate} {b = topNegate} refl ()
noTopMatch {a = topConjunction} {b = topConjunction} refl ()
noTopMatch {a = topDisjunction} {b = topDisjunction} refl ()
noTopMatch {a = topInvalid} {b = topInvalid} refl ()
noTopMatch {a = topVariable} {b = topFalse} () tt
noTopMatch {a = topVariable} {b = topTrue} () tt
noTopMatch {a = topVariable} {b = topNegate} () tt
noTopMatch {a = topVariable} {b = topConjunction} () tt
noTopMatch {a = topVariable} {b = topDisjunction} () tt
noTopMatch {a = topVariable} {b = topInvalid} () tt
noTopMatch {a = topFalse} {b = topVariable} () tt
noTopMatch {a = topFalse} {b = topTrue} () tt
noTopMatch {a = topFalse} {b = topNegate} () tt
noTopMatch {a = topFalse} {b = topConjunction} () tt
noTopMatch {a = topFalse} {b = topDisjunction} () tt
noTopMatch {a = topFalse} {b = topInvalid} () tt
noTopMatch {a = topTrue} {b = topVariable} () tt
noTopMatch {a = topTrue} {b = topFalse} () tt
noTopMatch {a = topTrue} {b = topNegate} () tt
noTopMatch {a = topTrue} {b = topConjunction} () tt
noTopMatch {a = topTrue} {b = topDisjunction} () tt
noTopMatch {a = topTrue} {b = topInvalid} () tt
noTopMatch {a = topNegate} {b = topVariable} () tt
noTopMatch {a = topNegate} {b = topFalse} () tt
noTopMatch {a = topNegate} {b = topTrue} () tt
noTopMatch {a = topNegate} {b = topConjunction} () tt
noTopMatch {a = topNegate} {b = topDisjunction} () tt
noTopMatch {a = topNegate} {b = topInvalid} () tt
noTopMatch {a = topConjunction} {b = topVariable} () tt
noTopMatch {a = topConjunction} {b = topFalse} () tt
noTopMatch {a = topConjunction} {b = topTrue} () tt
noTopMatch {a = topConjunction} {b = topNegate} () tt
noTopMatch {a = topConjunction} {b = topDisjunction} () tt
noTopMatch {a = topConjunction} {b = topInvalid} () tt
noTopMatch {a = topDisjunction} {b = topVariable} () tt
noTopMatch {a = topDisjunction} {b = topFalse} () tt
noTopMatch {a = topDisjunction} {b = topTrue} () tt
noTopMatch {a = topDisjunction} {b = topNegate} () tt
noTopMatch {a = topDisjunction} {b = topConjunction} () tt
noTopMatch {a = topDisjunction} {b = topInvalid} () tt
noTopMatch {a = topInvalid} {b = topVariable} () tt
noTopMatch {a = topInvalid} {b = topFalse} () tt
noTopMatch {a = topInvalid} {b = topTrue} () tt
noTopMatch {a = topInvalid} {b = topNegate} () tt
noTopMatch {a = topInvalid} {b = topConjunction} () tt
noTopMatch {a = topInvalid} {b = topDisjunction} () tt

parsedFormulaTopMatchesInput :
  (fuel : Nat)
  (token : Prefix.CookSyntaxToken)
  (rest : List Prefix.CookSyntaxToken)
  (formula : Cook.BooleanFormula)
  (suffix : List Prefix.CookSyntaxToken) →
  Prefix.parseCookFormulaFuel (suc fuel) (token ∷ rest) ≡
    Prefix.parsed formula suffix →
  formulaTop formula ≡ tokenTop token
parsedFormulaTopMatchesInput fuel Prefix.natZeroToken rest formula suffix eq =
  ⊥-elim (failureIsNotParsed eq)
parsedFormulaTopMatchesInput fuel Prefix.natSuccToken rest formula suffix eq =
  ⊥-elim (failureIsNotParsed eq)
parsedFormulaTopMatchesInput fuel
  Prefix.formulaFalseToken rest .(Cook.constant false) .rest refl = refl
parsedFormulaTopMatchesInput fuel
  Prefix.formulaTrueToken rest .(Cook.constant true) .rest refl = refl
parsedFormulaTopMatchesInput fuel
  Prefix.formulaVariableToken rest formula suffix eq
  with Prefix.parseNat rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
... | Prefix.parsed n afterNat with eq
...   | refl = refl
parsedFormulaTopMatchesInput fuel
  Prefix.formulaNegateToken rest formula suffix eq
  with Prefix.parseCookFormulaFuel fuel rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
... | Prefix.parsed child afterChild with eq
...   | refl = refl
parsedFormulaTopMatchesInput fuel
  Prefix.formulaAndToken rest formula suffix eq
  with Prefix.parseCookFormulaFuel fuel rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
... | Prefix.parsed left afterLeft
  with Prefix.parseCookFormulaFuel fuel afterLeft
...   | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
...   | Prefix.parsed right afterRight with eq
...     | refl = refl
parsedFormulaTopMatchesInput fuel
  Prefix.formulaOrToken rest formula suffix eq
  with Prefix.parseCookFormulaFuel fuel rest
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
... | Prefix.parsed left afterLeft
  with Prefix.parseCookFormulaFuel fuel afterLeft
...   | Prefix.parseFailure = ⊥-elim (failureIsNotParsed eq)
...   | Prefix.parsed right afterRight with eq
...     | refl = refl

-- Strong parser inverse: structural recursion is on the decoded
-- BooleanFormula, so both subformula calls in an AND/OR are smaller.
-- The second parse may consume a suffix discovered by the first.
------------------------------------------------------------------------

rebuildCookFuel :
  (formula : Cook.BooleanFormula)
  (fuel : Nat)
  (tokens suffix : List Prefix.CookSyntaxToken) →
  Prefix.parseCookFormulaFuel fuel tokens ≡ Prefix.parsed formula suffix →
  tokens ≡ Prefix.encodeCookFormulaInto formula suffix
rebuildCookFuel formula zero tokens suffix evidence =
  ⊥-elim (failureIsNotParsed evidence)
rebuildCookFuel (Cook.formulaVar index) (suc fuel) [] suffix evidence =
  ⊥-elim (failureIsNotParsed evidence)
rebuildCookFuel (Cook.formulaVar index) (suc fuel) (Prefix.natZeroToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natZeroToken rest (Cook.formulaVar index) suffix evidence) tt
rebuildCookFuel (Cook.formulaVar index) (suc fuel) (Prefix.natSuccToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natSuccToken rest (Cook.formulaVar index) suffix evidence) tt
rebuildCookFuel (Cook.formulaVar index) (suc fuel) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaFalseToken rest (Cook.formulaVar index) suffix evidence) tt
rebuildCookFuel (Cook.formulaVar index) (suc fuel) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaTrueToken rest (Cook.formulaVar index) suffix evidence) tt
rebuildCookFuel (Cook.formulaVar index) (suc fuel) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaNegateToken rest (Cook.formulaVar index) suffix evidence) tt
rebuildCookFuel (Cook.formulaVar index) (suc fuel) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaAndToken rest (Cook.formulaVar index) suffix evidence) tt
rebuildCookFuel (Cook.formulaVar index) (suc fuel) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaOrToken rest (Cook.formulaVar index) suffix evidence) tt
rebuildCookFuel (Cook.formulaVar index) (suc fuel)
  (Prefix.formulaVariableToken ∷ rest) suffix evidence
  with Prefix.parseNat rest in eqNat
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
... | Prefix.parsed parsedIndex parsedSuffix with evidence
...   | refl =
  cong (Prefix.formulaVariableToken ∷_)
    (natSuccessCanonical rest index suffix eqNat)

rebuildCookFuel (Cook.constant false) (suc fuel) [] suffix evidence =
  ⊥-elim (failureIsNotParsed evidence)
rebuildCookFuel (Cook.constant false) (suc fuel) (Prefix.natZeroToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natZeroToken rest (Cook.constant false) suffix evidence) tt
rebuildCookFuel (Cook.constant false) (suc fuel) (Prefix.natSuccToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natSuccToken rest (Cook.constant false) suffix evidence) tt
rebuildCookFuel (Cook.constant false) (suc fuel) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaVariableToken rest (Cook.constant false) suffix evidence) tt
rebuildCookFuel (Cook.constant false) (suc fuel) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaTrueToken rest (Cook.constant false) suffix evidence) tt
rebuildCookFuel (Cook.constant false) (suc fuel) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaNegateToken rest (Cook.constant false) suffix evidence) tt
rebuildCookFuel (Cook.constant false) (suc fuel) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaAndToken rest (Cook.constant false) suffix evidence) tt
rebuildCookFuel (Cook.constant false) (suc fuel) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaOrToken rest (Cook.constant false) suffix evidence) tt
rebuildCookFuel (Cook.constant false) (suc fuel)
  (Prefix.formulaFalseToken ∷ rest) .rest refl = refl

rebuildCookFuel (Cook.constant true) (suc fuel) [] suffix evidence =
  ⊥-elim (failureIsNotParsed evidence)
rebuildCookFuel (Cook.constant true) (suc fuel) (Prefix.natZeroToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natZeroToken rest (Cook.constant true) suffix evidence) tt
rebuildCookFuel (Cook.constant true) (suc fuel) (Prefix.natSuccToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natSuccToken rest (Cook.constant true) suffix evidence) tt
rebuildCookFuel (Cook.constant true) (suc fuel) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaVariableToken rest (Cook.constant true) suffix evidence) tt
rebuildCookFuel (Cook.constant true) (suc fuel) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaFalseToken rest (Cook.constant true) suffix evidence) tt
rebuildCookFuel (Cook.constant true) (suc fuel) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaNegateToken rest (Cook.constant true) suffix evidence) tt
rebuildCookFuel (Cook.constant true) (suc fuel) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaAndToken rest (Cook.constant true) suffix evidence) tt
rebuildCookFuel (Cook.constant true) (suc fuel) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaOrToken rest (Cook.constant true) suffix evidence) tt
rebuildCookFuel (Cook.constant true) (suc fuel)
  (Prefix.formulaTrueToken ∷ rest) .rest refl = refl

rebuildCookFuel (Cook.negate child) (suc fuel) [] suffix evidence =
  ⊥-elim (failureIsNotParsed evidence)
rebuildCookFuel (Cook.negate child) (suc fuel) (Prefix.natZeroToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natZeroToken rest (Cook.negate child) suffix evidence) tt
rebuildCookFuel (Cook.negate child) (suc fuel) (Prefix.natSuccToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natSuccToken rest (Cook.negate child) suffix evidence) tt
rebuildCookFuel (Cook.negate child) (suc fuel) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaVariableToken rest (Cook.negate child) suffix evidence) tt
rebuildCookFuel (Cook.negate child) (suc fuel) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaFalseToken rest (Cook.negate child) suffix evidence) tt
rebuildCookFuel (Cook.negate child) (suc fuel) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaTrueToken rest (Cook.negate child) suffix evidence) tt
rebuildCookFuel (Cook.negate child) (suc fuel) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaAndToken rest (Cook.negate child) suffix evidence) tt
rebuildCookFuel (Cook.negate child) (suc fuel) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaOrToken rest (Cook.negate child) suffix evidence) tt
rebuildCookFuel (Cook.negate child) (suc fuel)
  (Prefix.formulaNegateToken ∷ rest) suffix evidence
  with Prefix.parseCookFormulaFuel fuel rest in eqChild
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
... | Prefix.parsed parsedChild parsedSuffix with evidence
...   | refl =
  cong (Prefix.formulaNegateToken ∷_)
    (rebuildCookFuel child fuel rest suffix eqChild)

rebuildCookFuel (Cook.conjunction left right) (suc fuel) [] suffix evidence =
  ⊥-elim (failureIsNotParsed evidence)
rebuildCookFuel (Cook.conjunction left right) (suc fuel) (Prefix.natZeroToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natZeroToken rest (Cook.conjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.conjunction left right) (suc fuel) (Prefix.natSuccToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natSuccToken rest (Cook.conjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.conjunction left right) (suc fuel) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaVariableToken rest (Cook.conjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.conjunction left right) (suc fuel) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaFalseToken rest (Cook.conjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.conjunction left right) (suc fuel) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaTrueToken rest (Cook.conjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.conjunction left right) (suc fuel) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaNegateToken rest (Cook.conjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.conjunction left right) (suc fuel) (Prefix.formulaOrToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaOrToken rest (Cook.conjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.conjunction left right) (suc fuel)
  (Prefix.formulaAndToken ∷ rest) suffix evidence
  with Prefix.parseCookFormulaFuel fuel rest in eqLeft
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
... | Prefix.parsed parsedLeft afterLeft
  with Prefix.parseCookFormulaFuel fuel afterLeft in eqRight
...   | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
...   | Prefix.parsed parsedRight afterRight with evidence
...     | refl =
  cong (Prefix.formulaAndToken ∷_)
    (trans
      (rebuildCookFuel left fuel rest afterLeft eqLeft)
      (cong (Prefix.encodeCookFormulaInto left)
        (rebuildCookFuel right fuel afterLeft suffix eqRight)))

rebuildCookFuel (Cook.disjunction left right) (suc fuel) [] suffix evidence =
  ⊥-elim (failureIsNotParsed evidence)
rebuildCookFuel (Cook.disjunction left right) (suc fuel) (Prefix.natZeroToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natZeroToken rest (Cook.disjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.disjunction left right) (suc fuel) (Prefix.natSuccToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.natSuccToken rest (Cook.disjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.disjunction left right) (suc fuel) (Prefix.formulaVariableToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaVariableToken rest (Cook.disjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.disjunction left right) (suc fuel) (Prefix.formulaFalseToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaFalseToken rest (Cook.disjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.disjunction left right) (suc fuel) (Prefix.formulaTrueToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaTrueToken rest (Cook.disjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.disjunction left right) (suc fuel) (Prefix.formulaNegateToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaNegateToken rest (Cook.disjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.disjunction left right) (suc fuel) (Prefix.formulaAndToken ∷ rest) suffix evidence =
  noTopMatch
    (parsedFormulaTopMatchesInput fuel
      Prefix.formulaAndToken rest (Cook.disjunction left right) suffix evidence) tt
rebuildCookFuel (Cook.disjunction left right) (suc fuel)
  (Prefix.formulaOrToken ∷ rest) suffix evidence
  with Prefix.parseCookFormulaFuel fuel rest in eqLeft
... | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
... | Prefix.parsed parsedLeft afterLeft
  with Prefix.parseCookFormulaFuel fuel afterLeft in eqRight
...   | Prefix.parseFailure = ⊥-elim (failureIsNotParsed evidence)
...   | Prefix.parsed right afterRight with evidence
...     | refl =
  cong (Prefix.formulaOrToken ∷_)
    (trans
      (rebuildCookFuel left fuel rest afterLeft eqLeft)
      (cong (Prefix.encodeCookFormulaInto left)
        (rebuildCookFuel right fuel afterLeft suffix eqRight)))

rebuildCook :
  (formula : Cook.BooleanFormula)
  (tokens suffix : List Prefix.CookSyntaxToken) →
  Prefix.parseCookFormula tokens ≡ Prefix.parsed formula suffix →
  tokens ≡ Prefix.encodeCookFormulaInto formula suffix
rebuildCook formula tokens suffix evidence =
  rebuildCookFuel formula (Prefix.listLength tokens) tokens suffix evidence


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
  with Strict.strictDecodeThreeTokens rest in eqRest
... | nothing = ⊥-elim (nothingIsNotJust evidence)
... | just tailTokens with evidence
...   | refl
  rewrite bitsAfterDecode a b c
        | reencodeThreeTokens rest tailTokens eqRest =
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
  with Strict.strictDecodeThreeTokens word in eqTokens
... | nothing = ⊥-elim (nothingIsNotJust evidence)
... | just tokens with Prefix.parseCookFormula tokens in eqParse
...   | Prefix.parseFailure = ⊥-elim (nothingIsNotJust evidence)
...   | Prefix.parsed p (_ ∷ rest) =
  ⊥-elim (nothingIsNotJust evidence)
...   | Prefix.parsed p [] with evidence
...     | refl =
  trans
    (cong Binary.encodeTokenStream
      (sym (rebuildCook p tokens [] eqParse)))
    (reencodeThreeTokens word tokens eqTokens)
