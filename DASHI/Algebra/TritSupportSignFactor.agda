{-# OPTIONS --safe #-}
module DASHI.Algebra.TritSupportSignFactor where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)

------------------------------------------------------------------------
-- Exact support/sign factorisation for balanced ternary.
--
-- A trit is either inactive (zero) or active with one of two signs.
-- The sign is therefore gated by support rather than supplied for zero.

record ⊤ : Set where
  constructor tt

data Support : Set where
  inactive active : Support

data Sign : Set where
  negative positive : Sign

GatedSign : Support → Set
GatedSign inactive = ⊤
GatedSign active = Sign

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

------------------------------------------------------------------------
-- Involution cross-pollination.
--
-- Balanced-ternary involution preserves support and reverses only the gated
-- sign.  This is the exact algebraic seam used by codec mask/sign streams and
-- by involution-equivariant kernel surfaces.

flipSign : Sign → Sign
flipSign negative = positive
flipSign positive = negative

flipSign-involutive :
  ∀ sign →
  flipSign (flipSign sign) ≡ sign
flipSign-involutive negative = refl
flipSign-involutive positive = refl

supportSignInv : SupportSign → SupportSign
supportSignInv (inactive , tt) = inactive , tt
supportSignInv (active , sign) = active , flipSign sign

supportSignInv-involutive :
  ∀ x →
  supportSignInv (supportSignInv x) ≡ x
supportSignInv-involutive (inactive , tt) = refl
supportSignInv-involutive (active , negative) = refl
supportSignInv-involutive (active , positive) = refl

encode-inv-equivariant :
  ∀ t →
  encode (inv t) ≡ supportSignInv (encode t)
encode-inv-equivariant neg = refl
encode-inv-equivariant zer = refl
encode-inv-equivariant pos = refl

decode-inv-equivariant :
  ∀ x →
  decode (supportSignInv x) ≡ inv (decode x)
decode-inv-equivariant (inactive , tt) = refl
decode-inv-equivariant (active , negative) = refl
decode-inv-equivariant (active , positive) = refl

supportOf : Trit → Support
supportOf t = fst (encode t)

support-inv-invariant :
  ∀ t →
  supportOf (inv t) ≡ supportOf t
support-inv-invariant neg = refl
support-inv-invariant zer = refl
support-inv-invariant pos = refl

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
