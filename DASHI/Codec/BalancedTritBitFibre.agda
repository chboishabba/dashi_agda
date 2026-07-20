module DASHI.Codec.BalancedTritBitFibre where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)

------------------------------------------------------------------------
-- Exact support/sign factorisation of balanced ternary.
--
-- This is the typed form of the two-stream reading:
--   A = support/magnitude bit;
--   B = sign bit, present only on the non-zero fibre.
-- It is not a claim that Trit is primitively binary.

data Sign : Set where
  positiveSign : Sign
  negativeSign : Sign

data TritFibre : Set where
  zeroFibre : TritFibre
  signedFibre : Sign → TritFibre

encodeFibre : Trit → TritFibre
encodeFibre neg = signedFibre negativeSign
encodeFibre zer = zeroFibre
encodeFibre pos = signedFibre positiveSign

decodeFibre : TritFibre → Trit
decodeFibre zeroFibre = zer
decodeFibre (signedFibre positiveSign) = pos
decodeFibre (signedFibre negativeSign) = neg

decode-encode : ∀ t → decodeFibre (encodeFibre t) ≡ t
decode-encode neg = refl
decode-encode zer = refl
decode-encode pos = refl

encode-decode : ∀ f → encodeFibre (decodeFibre f) ≡ f
encode-decode zeroFibre = refl
encode-decode (signedFibre positiveSign) = refl
encode-decode (signedFibre negativeSign) = refl

------------------------------------------------------------------------
-- Explicit stream projections.

supportBit : TritFibre → Bool
supportBit zeroFibre = false
supportBit (signedFibre _) = true

data OptionalSignBit : Set where
  noSignBit : OptionalSignBit
  someSignBit : Bool → OptionalSignBit

signBit : TritFibre → OptionalSignBit
signBit zeroFibre = noSignBit
signBit (signedFibre positiveSign) = someSignBit false
signBit (signedFibre negativeSign) = someSignBit true

record BitStreamView : Set where
  constructor bits
  field
    magnitude : Bool
    sign : OptionalSignBit

bitStreamView : Trit → BitStreamView
bitStreamView t = bits (supportBit (encodeFibre t)) (signBit (encodeFibre t))

------------------------------------------------------------------------
-- Involution acts only in the signed fibre; zero remains fixed.

invertSign : Sign → Sign
invertSign positiveSign = negativeSign
invertSign negativeSign = positiveSign

invertFibre : TritFibre → TritFibre
invertFibre zeroFibre = zeroFibre
invertFibre (signedFibre s) = signedFibre (invertSign s)

invertFibre-involutive : ∀ f → invertFibre (invertFibre f) ≡ f
invertFibre-involutive zeroFibre = refl
invertFibre-involutive (signedFibre positiveSign) = refl
invertFibre-involutive (signedFibre negativeSign) = refl

encode-commutes-involution :
  ∀ t → encodeFibre (inv t) ≡ invertFibre (encodeFibre t)
encode-commutes-involution neg = refl
encode-commutes-involution zer = refl
encode-commutes-involution pos = refl

------------------------------------------------------------------------
-- Exact emitted bit count: one support bit per trit and one additional
-- sign bit precisely for each non-zero trit.

tritBitCost : Trit → Nat
tritBitCost neg = suc (suc zero)
tritBitCost zer = suc zero
tritBitCost pos = suc (suc zero)

wordBitCost : List Trit → Nat
wordBitCost [] = zero
wordBitCost (t ∷ ts) = tritBitCost t + wordBitCost ts

nonZeroCount : List Trit → Nat
nonZeroCount [] = zero
nonZeroCount (neg ∷ ts) = suc (nonZeroCount ts)
nonZeroCount (zer ∷ ts) = nonZeroCount ts
nonZeroCount (pos ∷ ts) = suc (nonZeroCount ts)

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

wordBitCost-support-plus-sign :
  ∀ ts → wordBitCost ts ≡ length ts + nonZeroCount ts
wordBitCost-support-plus-sign [] = refl
wordBitCost-support-plus-sign (neg ∷ ts)
  rewrite wordBitCost-support-plus-sign ts = refl
wordBitCost-support-plus-sign (zer ∷ ts)
  rewrite wordBitCost-support-plus-sign ts = refl
wordBitCost-support-plus-sign (pos ∷ ts)
  rewrite wordBitCost-support-plus-sign ts = refl
