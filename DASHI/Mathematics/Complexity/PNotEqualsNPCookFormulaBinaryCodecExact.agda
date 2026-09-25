module DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact where

------------------------------------------------------------------------
-- BINARY CODE FOR THE CLAY-CRITICAL COOK BOOLEANFORMULA
--
-- PNotEqualsNPCookFormulaPrefixCodecExact gives eight prefix syntax tokens.
-- Eight tokens fit exactly in three bits.
--
-- This owner serializes the prefix token stream to List Bool and proves:
--
--   decodeFormulaBits (encodeFormulaBits phi) = phi
--
-- together with the exact bit-length theorem:
--
--   bitLength (encodeFormulaBits phi)
--     = 3 * cookFormulaTokenCount phi.
--
-- This is a machine-independent finite input payload.  No assumption is made
-- yet that an arbitrary concrete tape machine has Bool as its literal Symbol
-- alphabet.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix

------------------------------------------------------------------------
-- Fixed three-bit token code.
------------------------------------------------------------------------

tokenBits :
  Prefix.CookSyntaxToken →
  List Bool
tokenBits Prefix.natZeroToken =
  false ∷ false ∷ false ∷ []
tokenBits Prefix.natSuccToken =
  false ∷ false ∷ true ∷ []
tokenBits Prefix.formulaVariableToken =
  false ∷ true ∷ false ∷ []
tokenBits Prefix.formulaFalseToken =
  false ∷ true ∷ true ∷ []
tokenBits Prefix.formulaTrueToken =
  true ∷ false ∷ false ∷ []
tokenBits Prefix.formulaNegateToken =
  true ∷ false ∷ true ∷ []
tokenBits Prefix.formulaAndToken =
  true ∷ true ∷ false ∷ []
tokenBits Prefix.formulaOrToken =
  true ∷ true ∷ true ∷ []

decodeTokenBits :
  Bool →
  Bool →
  Bool →
  Prefix.CookSyntaxToken
decodeTokenBits false false false =
  Prefix.natZeroToken
decodeTokenBits false false true =
  Prefix.natSuccToken
decodeTokenBits false true false =
  Prefix.formulaVariableToken
decodeTokenBits false true true =
  Prefix.formulaFalseToken
decodeTokenBits true false false =
  Prefix.formulaTrueToken
decodeTokenBits true false true =
  Prefix.formulaNegateToken
decodeTokenBits true true false =
  Prefix.formulaAndToken
decodeTokenBits true true true =
  Prefix.formulaOrToken

decodeThree :
  List Bool →
  Prefix.CookSyntaxToken
decodeThree
    (first ∷ second ∷ third ∷ rest) =
  decodeTokenBits first second third
decodeThree other =
  Prefix.natZeroToken

decodeTokenBitsAfterEncode :
  (token : Prefix.CookSyntaxToken) →
  decodeThree (tokenBits token) ≡ token
decodeTokenBitsAfterEncode Prefix.natZeroToken = refl
decodeTokenBitsAfterEncode Prefix.natSuccToken = refl
decodeTokenBitsAfterEncode Prefix.formulaVariableToken = refl
decodeTokenBitsAfterEncode Prefix.formulaFalseToken = refl
decodeTokenBitsAfterEncode Prefix.formulaTrueToken = refl
decodeTokenBitsAfterEncode Prefix.formulaNegateToken = refl
decodeTokenBitsAfterEncode Prefix.formulaAndToken = refl
decodeTokenBitsAfterEncode Prefix.formulaOrToken = refl

------------------------------------------------------------------------
-- List operations.
------------------------------------------------------------------------

append :
  ∀ {A : Set} →
  List A →
  List A →
  List A
append [] ys =
  ys
append (x ∷ xs) ys =
  x ∷ append xs ys

listLength :
  ∀ {A : Set} →
  List A →
  Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

appendLength :
  ∀ {A : Set}
    (left right : List A) →
  listLength (append left right)
  ≡ listLength left + listLength right
appendLength [] right =
  refl
appendLength (x ∷ xs) right
    rewrite appendLength xs right =
  refl

tokenBitsLength :
  (token : Prefix.CookSyntaxToken) →
  listLength (tokenBits token)
  ≡ suc (suc (suc zero))
tokenBitsLength Prefix.natZeroToken = refl
tokenBitsLength Prefix.natSuccToken = refl
tokenBitsLength Prefix.formulaVariableToken = refl
tokenBitsLength Prefix.formulaFalseToken = refl
tokenBitsLength Prefix.formulaTrueToken = refl
tokenBitsLength Prefix.formulaNegateToken = refl
tokenBitsLength Prefix.formulaAndToken = refl
tokenBitsLength Prefix.formulaOrToken = refl

------------------------------------------------------------------------
-- Token-stream binary serialization.
------------------------------------------------------------------------

encodeTokenStream :
  List Prefix.CookSyntaxToken →
  List Bool
encodeTokenStream [] =
  []
encodeTokenStream (token ∷ tokens) =
  append
    (tokenBits token)
    (encodeTokenStream tokens)

decodeTokenStream :
  List Bool →
  List Prefix.CookSyntaxToken
decodeTokenStream [] =
  []
decodeTokenStream
    (first ∷ second ∷ third ∷ rest) =
  decodeTokenBits first second third
  ∷ decodeTokenStream rest
decodeTokenStream (first ∷ []) =
  []
decodeTokenStream (first ∷ second ∷ []) =
  []

decodeEncodeTokenStream :
  (tokens : List Prefix.CookSyntaxToken) →
  decodeTokenStream
    (encodeTokenStream tokens)
  ≡ tokens
decodeEncodeTokenStream [] =
  refl
decodeEncodeTokenStream (token ∷ tokens)
    with token
... | Prefix.natZeroToken
    rewrite decodeEncodeTokenStream tokens =
  refl
... | Prefix.natSuccToken
    rewrite decodeEncodeTokenStream tokens =
  refl
... | Prefix.formulaVariableToken
    rewrite decodeEncodeTokenStream tokens =
  refl
... | Prefix.formulaFalseToken
    rewrite decodeEncodeTokenStream tokens =
  refl
... | Prefix.formulaTrueToken
    rewrite decodeEncodeTokenStream tokens =
  refl
... | Prefix.formulaNegateToken
    rewrite decodeEncodeTokenStream tokens =
  refl
... | Prefix.formulaAndToken
    rewrite decodeEncodeTokenStream tokens =
  refl
... | Prefix.formulaOrToken
    rewrite decodeEncodeTokenStream tokens =
  refl

encodeTokenStreamLength :
  (tokens : List Prefix.CookSyntaxToken) →
  listLength (encodeTokenStream tokens)
  ≡
  (suc (suc (suc zero))) * listLength tokens
encodeTokenStreamLength [] =
  refl
encodeTokenStreamLength (token ∷ tokens)
    rewrite
      appendLength
        (tokenBits token)
        (encodeTokenStream tokens)
      |
      tokenBitsLength token
      |
      encodeTokenStreamLength tokens =
  refl

------------------------------------------------------------------------
-- Formula-level binary code.
------------------------------------------------------------------------

encodeFormulaBits :
  Cook.BooleanFormula →
  List Bool
encodeFormulaBits formula =
  encodeTokenStream
    (Prefix.encodeCookFormula formula)

decodeFormulaBits :
  List Bool →
  Cook.BooleanFormula
decodeFormulaBits bits =
  Prefix.decodeCookFormula
    (decodeTokenStream bits)

decodeEncodeFormulaBits :
  (formula : Cook.BooleanFormula) →
  decodeFormulaBits
    (encodeFormulaBits formula)
  ≡ formula
decodeEncodeFormulaBits formula
    rewrite
      decodeEncodeTokenStream
        (Prefix.encodeCookFormula formula)
      |
      Prefix.decodeEncodeCookFormula formula =
  refl

formulaBitCodeLength :
  Cook.BooleanFormula →
  Nat
formulaBitCodeLength formula =
  listLength
    (encodeFormulaBits formula)

formulaBitCodeLengthExact :
  (formula : Cook.BooleanFormula) →
  formulaBitCodeLength formula
  ≡
  (suc (suc (suc zero)))
  * Prefix.cookFormulaTokenCount formula
formulaBitCodeLengthExact formula
    rewrite
      encodeTokenStreamLength
        (Prefix.encodeCookFormula formula)
      |
      Prefix.encodeCookFormulaLength formula =
  refl

------------------------------------------------------------------------
-- Research boundary.
--
-- The self-reference programme now has a concrete finite binary code for the
-- exact Cook formula carrier.
--
-- Still separate:
--
--   * realizing List Bool as InputWord of an arbitrary candidate machine;
--   * constructing a described binary-input SAT machine;
--   * resource-bounded self-instantiation/fixed point.
------------------------------------------------------------------------
