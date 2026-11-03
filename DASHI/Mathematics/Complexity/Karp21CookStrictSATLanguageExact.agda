{-# OPTIONS --safe #-}

module DASHI.Mathematics.Complexity.Karp21CookStrictSATLanguageExact where

------------------------------------------------------------------------
-- K00 REAL BINARY SAT LANGUAGE, source/decoder/acceptance SAME OBJECT.
--
-- Reuse Cook.BooleanFormula from the actual DASHI Clay SAT carrier,
-- existing exact prefix/formula code, and the new total STRICT parser.
-- Reject invalid code (not "decode bad input to FALSE formula").
--
-- Theorems:
--   accepts(encodeFormulaBits phi) iff Cook.Satisfiable phi;
--   1/2 dangling bits and a whole extra syntactic token are REJECTED.
--
-- SAT hardness for all NP languages and the encoding's exact tape cost
-- remain independent. This does not manufacture the Cook-Levin root.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; nothing; just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Bits
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict

StrictSATAccepts : Word.BitWord → Set
StrictSATAccepts word with Strict.strictDecodeCookFormulaBits word
... | nothing = ⊥
... | just formula = Cook.Satisfiable formula

strictSATLanguage : PR.Language Word.BitWord
strictSATLanguage = record { PR.accepts = StrictSATAccepts }

-- Real SAT language roundtrip on every Cook formula, not merely token
-- equality, with impossible malformed syntax excluded by the parser.
strictSATFormulaWordIff :
  (formula : Cook.BooleanFormula) →
  PR.Iff (Cook.Satisfiable formula)
    (PR.accepts strictSATLanguage (Bits.encodeFormulaBits formula))
strictSATFormulaWordIff formula
  rewrite Strict.strictCookFormulaRoundTrip formula =
  PR.iff (λ p → p) (λ p → p)

-- The malformed word examples are actual *rejected SAT instances*,
-- not merely a parser flag; the trailing terminal bits cannot be
-- misinterpreted as an accepting prefix SAT problem.
strictSATRejectsOneTrailingBit :
  (formula : Cook.BooleanFormula) (extra : Bool) →
  PR.accepts strictSATLanguage
    (Bits.append (Bits.encodeFormulaBits formula) (extra ∷ [])) →
  ⊥
strictSATRejectsOneTrailingBit formula extra
  rewrite Strict.strictRejectOneExtraBit
    (Prefix.encodeCookFormula formula) extra =
  λ ()

strictSATRejectsTwoTrailingBits :
  (formula : Cook.BooleanFormula) (first second : Bool) →
  PR.accepts strictSATLanguage
    (Bits.append (Bits.encodeFormulaBits formula)
      (first ∷ second ∷ [])) →
  ⊥
strictSATRejectsTwoTrailingBits formula first second
  rewrite Strict.strictRejectTwoExtraBits
    (Prefix.encodeCookFormula formula) first second =
  λ ()

strictSATRejectsCompleteExtraToken :
  (formula : Cook.BooleanFormula) →
  PR.accepts strictSATLanguage
    (Bits.encodeTokenStream
      (Prefix.encodeCookFormulaInto formula
        (Prefix.formulaFalseToken ∷ []))) → ⊥
strictSATRejectsCompleteExtraToken formula
  rewrite Strict.strictRejectTrailingCompleteFormulaToken formula =
  λ ()
