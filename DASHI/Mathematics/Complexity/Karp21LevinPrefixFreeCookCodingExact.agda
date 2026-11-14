module DASHI.Mathematics.Complexity.Karp21LevinPrefixFreeCookCodingExact where

------------------------------------------------------------------------
-- PRE-EXISTING MICHAEL LEVIN CODING BOUNDARY: real proof upgrade.
--
-- DASHI.Biology.Levin.PrefixFreeCodingBoundary has a coding-status
-- record with Bool fields. Those are NOT prefix-free proof terms.
-- Here we discharge one exact mathematical part for the existing
-- Cook SAT prefix representation. The result is a typed proof that
-- a complete Cook formula cannot swallow an appended token suffix.
--
-- For the actual binary encoder, the same property holds when the
-- suffix consists of complete source-owned THREE-BIT syntax tokens:
--    encodeTokenStream (encodeCookFormulaInto p suffix)
--       = encodeFormulaBits q
--  implies suffix = [].
-- It is not yet arbitrary-bit prefix-freeness (trailing 1/2 bits
-- need the separate strict decoder from Karp21CookStrictTriple...).
--
-- The parser theorem is *already source-written* in:
--   PNotEqualsNPCookFormulaPrefixCodecExact.parseCookFormulaEncodeInto.
-- Karp's SAT problem and Michael Levin's biological coding boundary
-- are not asserted to be a shared biological mechanism.
-- Author roots: Cook 1971; independent DASHI Cook codec owners;
-- original Levin boundary retained read-only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Maybe.Base as Maybe
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Biology.Levin.PrefixFreeCodingBoundary as LevinCoding
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict

-- Reuse the original PREFIX parser that preserves the unconsumed suffix.
-- If another FULL formula has this encoding, the first formula must
-- have consumed *exactly* the full input, not an extension.
cookPrefixSuffixMustBeEmpty :
  (left right : Cook.BooleanFormula)
  (suffix : List Prefix.CookSyntaxToken) →
  Prefix.encodeCookFormulaInto left suffix
    ≡ Prefix.encodeCookFormula right →
  suffix ≡ []
cookPrefixSuffixMustBeEmpty left right suffix equality =
  extractSuffix
    (trans
      (sym (Prefix.parseCookFormulaEncodeInto left suffix))
      (trans
        (cong Prefix.parseCookFormula equality)
        (Prefix.parseEncodedCookFormula right)))
  where
    extractSuffix :
      ∀ {first second : Cook.BooleanFormula}
        {rest : List Prefix.CookSyntaxToken} →
      Prefix.parsed first rest ≡ Prefix.parsed second [] →
      rest ≡ []
    extractSuffix refl = refl

-- The same argument on the binary output uses the actual strict
-- three-bit token decoder as a LEFT INVERSE of encodeTokenStream.
-- It does not use the prior boolean prefixFreeWitness flag.
cookCompleteTokenBinarySuffixMustBeEmpty :
  (left right : Cook.BooleanFormula)
  (suffix : List Prefix.CookSyntaxToken) →
  Binary.encodeTokenStream (Prefix.encodeCookFormulaInto left suffix)
    ≡ Binary.encodeFormulaBits right →
  suffix ≡ []
cookCompleteTokenBinarySuffixMustBeEmpty left right suffix equality =
  cookPrefixSuffixMustBeEmpty left right suffix
    (decodeJust
      (trans
        (sym (Strict.strictDecodeThreeTokensAfterEncode
          (Prefix.encodeCookFormulaInto left suffix)))
        (trans
          (cong Strict.strictDecodeThreeTokens equality)
          (Strict.strictCookFormulaTokenRoundTrip right))))
  where
    decodeJust :
      ∀ {a b : List Prefix.CookSyntaxToken} →
      Maybe.just a ≡ Maybe.just b →
      a ≡ b
    decodeJust refl = refl

-- Unlike the bio coding-status record's Bool field, this is a real
-- source proof of no proper suffix in the complete-token sublanguage.
record CookCompleteTokenPrefixWitness : Set where
  field
    suffixExclusion :
      (left right : Cook.BooleanFormula)
      (suffix : List Prefix.CookSyntaxToken) →
      Binary.encodeTokenStream
        (Prefix.encodeCookFormulaInto left suffix)
        ≡ Binary.encodeFormulaBits right →
      suffix ≡ []

cookCompleteTokenPrefixWitness : CookCompleteTokenPrefixWitness
cookCompleteTokenPrefixWitness = record
  { CookCompleteTokenPrefixWitness.suffixExclusion =
      cookCompleteTokenBinarySuffixMustBeEmpty }
