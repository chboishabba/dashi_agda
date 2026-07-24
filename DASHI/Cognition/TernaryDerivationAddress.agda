module DASHI.Cognition.TernaryDerivationAddress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Algebra.BalancedTernary as BT

------------------------------------------------------------------------
-- Balanced trits are mapped to ordinary base-three digits.  The first token
-- is the least-significant digit, matching the p-adic convention that early
-- derivation decisions determine the coarse cylinder and later tokens refine
-- within it.
------------------------------------------------------------------------

tritDigit : BT.Trit → Nat
tritDigit BT.neg = 0
tritDigit BT.zero = 1
tritDigit BT.pos = 2

encode3 : List BT.Trit → Nat
encode3 [] = 0
encode3 (token ∷ tokens) = tritDigit token + 3 * encode3 tokens

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

record Finite3AdicAddress : Set where
  constructor finite3AdicAddress
  field
    digits : List BT.Trit
    encoded : Nat
    encodingCorrect : encoded ≡ encode3 digits

address : List BT.Trit → Finite3AdicAddress
address digits = finite3AdicAddress digits (encode3 digits) refl

emptyAddressIsZero : encode3 [] ≡ 0
emptyAddressIsZero = refl

negativeZeroPositiveAddress :
  encode3 (BT.neg ∷ BT.zero ∷ BT.pos ∷ []) ≡ 21
negativeZeroPositiveAddress = refl

allPositiveThreeDigitAddress :
  encode3 (BT.pos ∷ BT.pos ∷ BT.pos ∷ []) ≡ 26
allPositiveThreeDigitAddress = refl

threeCubedIsTwentySeven : pow3 3 ≡ 27
threeCubedIsTwentySeven = refl
