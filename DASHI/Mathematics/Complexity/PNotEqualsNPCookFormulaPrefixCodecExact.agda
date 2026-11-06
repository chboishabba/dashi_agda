{-# OPTIONS --safe #-}

module DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact where

------------------------------------------------------------------------
-- PREFIX CODE FOR THE CLAY-CRITICAL COOK BOOLEANFORMULA
--
-- Resource-bounded self-reference needs finite syntax for the ACTUAL formula
-- carrier consumed by SATLowerBoundProducer.
--
-- This owner gives a concrete prefix token stream:
--
--   variable n   -> formulaVariableToken ++ unaryNat(n)
--   false        -> formulaFalseToken
--   true         -> formulaTrueToken
--   not p        -> formulaNegateToken ++ code(p)
--   p and q      -> formulaAndToken ++ code(p) ++ code(q)
--   p or q       -> formulaOrToken  ++ code(p) ++ code(q)
--
-- The parser is suffix-preserving, so concatenated recursive codes are
-- unambiguous.  Main theorem:
--
--   decodeCookFormula (encodeCookFormula phi) = phi.
--
-- A second theorem gives the exact token count.  This is the quantitative
-- quotation surface needed by the bounded fixed-point programme.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Empty using (⊥-elim)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook

------------------------------------------------------------------------
-- Tokens and parser result.
------------------------------------------------------------------------

data CookSyntaxToken : Set where
  natZeroToken natSuccToken : CookSyntaxToken
  formulaVariableToken : CookSyntaxToken
  formulaFalseToken formulaTrueToken : CookSyntaxToken
  formulaNegateToken formulaAndToken formulaOrToken : CookSyntaxToken

data ParseResult (A : Set) : Set where
  parseFailure : ParseResult A
  parsed : A → List CookSyntaxToken → ParseResult A

------------------------------------------------------------------------
-- Prefix encoder.
------------------------------------------------------------------------

encodeNatInto :
  Nat →
  List CookSyntaxToken →
  List CookSyntaxToken
encodeNatInto zero rest =
  natZeroToken ∷ rest
encodeNatInto (suc n) rest =
  natSuccToken ∷ encodeNatInto n rest

encodeCookFormulaInto :
  Cook.BooleanFormula →
  List CookSyntaxToken →
  List CookSyntaxToken
encodeCookFormulaInto
    (Cook.formulaVar index)
    rest =
  formulaVariableToken
  ∷ encodeNatInto index rest
encodeCookFormulaInto
    (Cook.constant false)
    rest =
  formulaFalseToken ∷ rest
encodeCookFormulaInto
    (Cook.constant true)
    rest =
  formulaTrueToken ∷ rest
encodeCookFormulaInto
    (Cook.negate formula)
    rest =
  formulaNegateToken
  ∷ encodeCookFormulaInto formula rest
encodeCookFormulaInto
    (Cook.conjunction left right)
    rest =
  formulaAndToken
  ∷ encodeCookFormulaInto
      left
      (encodeCookFormulaInto right rest)
encodeCookFormulaInto
    (Cook.disjunction left right)
    rest =
  formulaOrToken
  ∷ encodeCookFormulaInto
      left
      (encodeCookFormulaInto right rest)

encodeCookFormula :
  Cook.BooleanFormula →
  List CookSyntaxToken
encodeCookFormula formula =
  encodeCookFormulaInto formula []

------------------------------------------------------------------------
-- Parser.
------------------------------------------------------------------------

parseNat :
  List CookSyntaxToken →
  ParseResult Nat
parseNat [] =
  parseFailure
parseNat (natZeroToken ∷ rest) =
  parsed zero rest
parseNat (natSuccToken ∷ rest)
    with parseNat rest
... | parseFailure =
  parseFailure
... | parsed n suffix =
  parsed (suc n) suffix
parseNat (_ ∷ _) =
  parseFailure

------------------------------------------------------------------------
-- Termination is on explicit fuel, never on the opaque suffix returned
-- by a recursive parse. On a successful encoded formula, the original
-- entire input word length supplies enough fuel for both subformulae.
------------------------------------------------------------------------

listLength :
  ∀ {A : Set} →
  List A →
  Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

parseCookFormulaFuel :
  Nat →
  List CookSyntaxToken →
  ParseResult Cook.BooleanFormula
parseCookFormulaFuel zero tokens = parseFailure
parseCookFormulaFuel (suc fuel) [] = parseFailure
parseCookFormulaFuel (suc fuel) (formulaVariableToken ∷ rest)
  with parseNat rest
... | parseFailure = parseFailure
... | parsed index suffix = parsed (Cook.formulaVar index) suffix
parseCookFormulaFuel (suc fuel) (formulaFalseToken ∷ rest) =
  parsed (Cook.constant false) rest
parseCookFormulaFuel (suc fuel) (formulaTrueToken ∷ rest) =
  parsed (Cook.constant true) rest
parseCookFormulaFuel (suc fuel) (formulaNegateToken ∷ rest)
  with parseCookFormulaFuel fuel rest
... | parseFailure = parseFailure
... | parsed formula suffix = parsed (Cook.negate formula) suffix
parseCookFormulaFuel (suc fuel) (formulaAndToken ∷ rest)
  with parseCookFormulaFuel fuel rest
... | parseFailure = parseFailure
... | parsed left afterLeft
  with parseCookFormulaFuel fuel afterLeft
...   | parseFailure = parseFailure
...   | parsed right suffix = parsed (Cook.conjunction left right) suffix
parseCookFormulaFuel (suc fuel) (formulaOrToken ∷ rest)
  with parseCookFormulaFuel fuel rest
... | parseFailure = parseFailure
... | parsed left afterLeft
  with parseCookFormulaFuel fuel afterLeft
...   | parseFailure = parseFailure
...   | parsed right suffix = parsed (Cook.disjunction left right) suffix
parseCookFormulaFuel (suc fuel) (_ ∷ _) = parseFailure

parseCookFormula :
  List CookSyntaxToken →
  ParseResult Cook.BooleanFormula
parseCookFormula tokens =
  parseCookFormulaFuel (listLength tokens) tokens

------------------------------------------------------------------------
-- Suffix-preserving roundtrip.
------------------------------------------------------------------------

parseNatEncodeInto :
  (n : Nat) →
  (suffix : List CookSyntaxToken) →
  parseNat (encodeNatInto n suffix)
  ≡ parsed n suffix
parseNatEncodeInto zero suffix =
  refl
parseNatEncodeInto (suc n) suffix
    rewrite parseNatEncodeInto n suffix =
  refl

------------------------------------------------------------------------
-- An encoder cannot shorten its continuation. Consequently any
-- fuel bound for an encoded binary formula also bounds the right child.
------------------------------------------------------------------------

encodeNatIntoSuffixLower :
  (n : Nat) (suffix : List CookSyntaxToken) →
  listLength suffix ≤ listLength (encodeNatInto n suffix)
encodeNatIntoSuffixLower zero suffix =
  NatP.≤-step NatP.≤-refl
encodeNatIntoSuffixLower (suc n) suffix =
  NatP.≤-step (encodeNatIntoSuffixLower n suffix)

encodeCookFormulaIntoSuffixLower :
  (formula : Cook.BooleanFormula) (suffix : List CookSyntaxToken) →
  listLength suffix ≤ listLength (encodeCookFormulaInto formula suffix)
encodeCookFormulaIntoSuffixLower (Cook.formulaVar n) suffix =
  NatP.≤-step (encodeNatIntoSuffixLower n suffix)
encodeCookFormulaIntoSuffixLower (Cook.constant false) suffix =
  NatP.≤-step NatP.≤-refl
encodeCookFormulaIntoSuffixLower (Cook.constant true) suffix =
  NatP.≤-step NatP.≤-refl
encodeCookFormulaIntoSuffixLower (Cook.negate f) suffix =
  NatP.≤-step (encodeCookFormulaIntoSuffixLower f suffix)
encodeCookFormulaIntoSuffixLower (Cook.conjunction f g) suffix =
  NatP.≤-step
    (NatP.≤-trans
      (encodeCookFormulaIntoSuffixLower g suffix)
      (encodeCookFormulaIntoSuffixLower f
        (encodeCookFormulaInto g suffix)))
encodeCookFormulaIntoSuffixLower (Cook.disjunction f g) suffix =
  NatP.≤-step
    (NatP.≤-trans
      (encodeCookFormulaIntoSuffixLower g suffix)
      (encodeCookFormulaIntoSuffixLower f
        (encodeCookFormulaInto g suffix)))

-- This stronger induction statement makes the fuel sufficient without
-- assuming that the right child is a syntactic tail of the left child.
parseCookFormulaFuelEncodeInto :
  (formula : Cook.BooleanFormula) →
  (suffix : List CookSyntaxToken) →
  (fuel : Nat) →
  listLength (encodeCookFormulaInto formula suffix) ≤ fuel →
  parseCookFormulaFuel fuel (encodeCookFormulaInto formula suffix)
    ≡ parsed formula suffix
parseCookFormulaFuelEncodeInto (Cook.formulaVar n) suffix zero ()
parseCookFormulaFuelEncodeInto (Cook.formulaVar n) suffix
    (suc fuel) (s≤s enough)
  rewrite parseNatEncodeInto n suffix = refl
parseCookFormulaFuelEncodeInto (Cook.constant false) suffix zero ()
parseCookFormulaFuelEncodeInto (Cook.constant false) suffix
    (suc fuel) (s≤s enough) = refl
parseCookFormulaFuelEncodeInto (Cook.constant true) suffix zero ()
parseCookFormulaFuelEncodeInto (Cook.constant true) suffix
    (suc fuel) (s≤s enough) = refl
parseCookFormulaFuelEncodeInto (Cook.negate f) suffix zero ()
parseCookFormulaFuelEncodeInto (Cook.negate f) suffix
    (suc fuel) (s≤s enough)
  rewrite parseCookFormulaFuelEncodeInto f suffix fuel enough = refl
parseCookFormulaFuelEncodeInto (Cook.conjunction left right) suffix zero ()
parseCookFormulaFuelEncodeInto (Cook.conjunction left right) suffix
    (suc fuel) (s≤s enough)
  rewrite parseCookFormulaFuelEncodeInto
    left (encodeCookFormulaInto right suffix) fuel enough
    | parseCookFormulaFuelEncodeInto right suffix fuel
      (NatP.≤-trans
        (encodeCookFormulaIntoSuffixLower left
          (encodeCookFormulaInto right suffix))
        enough) = refl
parseCookFormulaFuelEncodeInto (Cook.disjunction left right) suffix zero ()
parseCookFormulaFuelEncodeInto (Cook.disjunction left right) suffix
    (suc fuel) (s≤s enough)
  rewrite parseCookFormulaFuelEncodeInto
    left (encodeCookFormulaInto right suffix) fuel enough
    | parseCookFormulaFuelEncodeInto right suffix fuel
      (NatP.≤-trans
        (encodeCookFormulaIntoSuffixLower left
          (encodeCookFormulaInto right suffix))
        enough) = refl

parseCookFormulaEncodeInto :
  (formula : Cook.BooleanFormula) →
  (suffix : List CookSyntaxToken) →
  parseCookFormula (encodeCookFormulaInto formula suffix)
    ≡ parsed formula suffix
parseCookFormulaEncodeInto formula suffix =
  parseCookFormulaFuelEncodeInto
    formula suffix
    (listLength (encodeCookFormulaInto formula suffix))
    NatP.≤-refl

parseEncodedCookFormula :
  (formula : Cook.BooleanFormula) →
  parseCookFormula
    (encodeCookFormula formula)
  ≡ parsed formula []
parseEncodedCookFormula formula =
  parseCookFormulaEncodeInto formula []

decodeCookFormula :
  List CookSyntaxToken →
  Cook.BooleanFormula
decodeCookFormula tokens
    with parseCookFormula tokens
... | parseFailure =
  Cook.constant false
... | parsed formula suffix =
  formula

decodeEncodeCookFormula :
  (formula : Cook.BooleanFormula) →
  decodeCookFormula
    (encodeCookFormula formula)
  ≡ formula
decodeEncodeCookFormula formula
    rewrite parseEncodedCookFormula formula =
  refl

------------------------------------------------------------------------
-- Exact token accounting.
------------------------------------------------------------------------

natTokenCount :
  Nat →
  Nat
natTokenCount zero =
  suc zero
natTokenCount (suc n) =
  suc (natTokenCount n)

cookFormulaTokenCount :
  Cook.BooleanFormula →
  Nat
cookFormulaTokenCount
    (Cook.formulaVar index) =
  suc (natTokenCount index)
cookFormulaTokenCount
    (Cook.constant value) =
  suc zero
cookFormulaTokenCount
    (Cook.negate formula) =
  suc (cookFormulaTokenCount formula)
cookFormulaTokenCount
    (Cook.conjunction left right) =
  suc
    (cookFormulaTokenCount left
     + cookFormulaTokenCount right)
cookFormulaTokenCount
    (Cook.disjunction left right) =
  suc
    (cookFormulaTokenCount left
     + cookFormulaTokenCount right)

encodeNatIntoLength :
  (n : Nat) →
  (suffix : List CookSyntaxToken) →
  listLength (encodeNatInto n suffix)
  ≡ natTokenCount n + listLength suffix
encodeNatIntoLength zero suffix =
  refl
encodeNatIntoLength (suc n) suffix
    rewrite encodeNatIntoLength n suffix =
  refl

encodeCookFormulaIntoLength :
  (formula : Cook.BooleanFormula) →
  (suffix : List CookSyntaxToken) →
  listLength
    (encodeCookFormulaInto formula suffix)
  ≡
  cookFormulaTokenCount formula
  + listLength suffix
encodeCookFormulaIntoLength
    (Cook.formulaVar index)
    suffix
    rewrite encodeNatIntoLength index suffix =
  refl
encodeCookFormulaIntoLength
    (Cook.constant false)
    suffix =
  refl
encodeCookFormulaIntoLength
    (Cook.constant true)
    suffix =
  refl
encodeCookFormulaIntoLength
    (Cook.negate formula)
    suffix
    rewrite
      encodeCookFormulaIntoLength
        formula
        suffix =
  refl
encodeCookFormulaIntoLength
    (Cook.conjunction left right)
    suffix
    rewrite
      encodeCookFormulaIntoLength
        left
        (encodeCookFormulaInto right suffix)
      |
      encodeCookFormulaIntoLength
        right
        suffix =
  reassociate
  where
    reassociate :
      suc
        (cookFormulaTokenCount left
         + (cookFormulaTokenCount right
            + listLength suffix))
      ≡
      suc
        (cookFormulaTokenCount left
         + cookFormulaTokenCount right)
      + listLength suffix
    reassociate =
      plusAssociative
        (cookFormulaTokenCount left)
        (cookFormulaTokenCount right)
        (listLength suffix)
      where
        plusAssociative :
          (a b c : Nat) →
          suc (a + (b + c))
          ≡ suc (a + b) + c
        plusAssociative zero b c =
          refl
        plusAssociative (suc a) b c =
          congSuc (plusAssociative a b c)
          where
            congSuc :
              ∀ {x y : Nat} →
              x ≡ y →
              suc x ≡ suc y
            congSuc refl = refl
encodeCookFormulaIntoLength
    (Cook.disjunction left right)
    suffix
    rewrite
      encodeCookFormulaIntoLength
        left
        (encodeCookFormulaInto right suffix)
      |
      encodeCookFormulaIntoLength
        right
        suffix =
  reassociate
  where
    reassociate :
      suc
        (cookFormulaTokenCount left
         + (cookFormulaTokenCount right
            + listLength suffix))
      ≡
      suc
        (cookFormulaTokenCount left
         + cookFormulaTokenCount right)
      + listLength suffix
    reassociate =
      plusAssociative
        (cookFormulaTokenCount left)
        (cookFormulaTokenCount right)
        (listLength suffix)
      where
        plusAssociative :
          (a b c : Nat) →
          suc (a + (b + c))
          ≡ suc (a + b) + c
        plusAssociative zero b c =
          refl
        plusAssociative (suc a) b c =
          congSuc (plusAssociative a b c)
          where
            congSuc :
              ∀ {x y : Nat} →
              x ≡ y →
              suc x ≡ suc y
            congSuc refl = refl

encodeCookFormulaLength :
  (formula : Cook.BooleanFormula) →
  listLength (encodeCookFormula formula)
  ≡ cookFormulaTokenCount formula
encodeCookFormulaLength formula
    with
      encodeCookFormulaIntoLength
        formula
        []
... | equality =
  equality

------------------------------------------------------------------------
-- Quotation never has zero token length.
------------------------------------------------------------------------

cookFormulaTokenCountPositive :
  (formula : Cook.BooleanFormula) →
  suc zero ≤ cookFormulaTokenCount formula
cookFormulaTokenCountPositive
    (Cook.formulaVar index) =
  s≤s z≤n
cookFormulaTokenCountPositive
    (Cook.constant value) =
  s≤s z≤n
cookFormulaTokenCountPositive
    (Cook.negate formula) =
  s≤s z≤n
cookFormulaTokenCountPositive
    (Cook.conjunction left right) =
  s≤s z≤n
cookFormulaTokenCountPositive
    (Cook.disjunction left right) =
  s≤s z≤n

------------------------------------------------------------------------
-- Research boundary.
--
-- This pays finite quotation and exact quotation length only.
--
-- It does NOT prove that an arbitrary concrete tape alphabet can carry these
-- tokens injectively, and it does NOT assert a literal self-code fixed point.
-- Those are separate obligations.
------------------------------------------------------------------------
