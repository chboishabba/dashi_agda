module DASHI.Algebra.TritSupportSignFactor where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- Exact support/sign factorisation for balanced ternary.
--
-- A trit is either inactive (zero) or active with one of two signs.
-- The sign is therefore gated by support rather than supplied for zero.


data Support : Set where
  inactive active : Support


data Sign : Set where
  negative positive : Sign

GatedSign : Support → Set
GatedSign inactive = ⊤
GatedSign active = Sign

record ⊤ : Set where
  constructor tt

SupportSign : Set
SupportSign = Σ Support GatedSign

encode : Trit → SupportSign
encode neg = active , negative
encode zer = inactive , tt
encode pos = active , positive

decode : SupportSign → Trit
decode (inactive , tt) = zer
decode (active , negative) = neg
decode (active , positive) = pos

decode-encode :
  ∀ t →
  decode (encode t) ≡ t
decode-encode neg = refl
decode-encode zer = refl
decode-encode pos = refl

encode-decode :
  ∀ x →
  encode (decode x) ≡ x
encode-decode (inactive , tt) = refl
encode-decode (active , negative) = refl
encode-decode (active , positive) = refl

record ExactSupportSignFactorisation : Set where
  field
    forward : Trit → SupportSign
    backward : SupportSign → Trit
    backward-forward : ∀ t → backward (forward t) ≡ t
    forward-backward : ∀ x → forward (backward x) ≡ x

tritSupportSignFactorisation : ExactSupportSignFactorisation
tritSupportSignFactorisation = record
  { forward = encode
  ; backward = decode
  ; backward-forward = decode-encode
  ; forward-backward = encode-decode
  }
