{-# OPTIONS --safe #-}
module DASHI.Interop.JMDRoundTripFixedPointExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; _⊔_)

private
  cong :
    {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} →
    (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  trans :
    {ℓ : Level} {A : Set ℓ} {x y z : A} →
    x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

------------------------------------------------------------------------
-- Conditional semantic fixed points.
-- The compiler adapters MUST supply the two inverse-law witnesses:
-- source names, AST hashes, translation modes, or OEIS/QID coordinates
-- do not themselves construct these witnesses.
------------------------------------------------------------------------

record CertifiedRoundTrip {ℓA ℓB : Level}
  (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where
  constructor certified-round-trip
  field
    toB : A → B
    toA : B → A
    leftInverse : (a : A) → toA (toB a) ≡ a
    rightInverse : (b : B) → toB (toA b) ≡ b

open CertifiedRoundTrip public

leanAgdaLeanStable :
  {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} →
  (r : CertifiedRoundTrip A B) → (a : A) →
  toA r (toB r a) ≡ a
leanAgdaLeanStable = leftInverse

agdaLeanAgdaStable :
  {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} →
  (r : CertifiedRoundTrip A B) → (b : B) →
  toB r (toA r b) ≡ b
agdaLeanAgdaStable = rightInverse

roundTripIdempotentLeft :
  {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} →
  (r : CertifiedRoundTrip A B) → (a : A) →
  toA r (toB r (toA r (toB r a))) ≡ a
roundTripIdempotentLeft r a =
  trans (cong (λ x → toA r (toB r x)) (leftInverse r a))
        (leftInverse r a)

roundTripIdempotentRight :
  {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} →
  (r : CertifiedRoundTrip A B) → (b : B) →
  toB r (toA r (toB r (toA r b))) ≡ b
roundTripIdempotentRight r b =
  trans (cong (λ x → toB r (toA r x)) (rightInverse r b))
        (rightInverse r b)

observerRoundTrip :
  {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
  (r : CertifiedRoundTrip A B) →
  (observe : A → C) → (a : A) →
  observe (toA r (toB r a)) ≡ observe a
observerRoundTrip r observe a = cong observe (leftInverse r a)

composeRoundTrip :
  {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
  CertifiedRoundTrip A B →
  CertifiedRoundTrip B C →
  CertifiedRoundTrip A C
composeRoundTrip ab bc = certified-round-trip
  (λ a → toB bc (toB ab a))
  (λ c → toA ab (toA bc c))
  (λ a →
    trans
      (cong (toA ab) (leftInverse bc (toB ab a)))
      (leftInverse ab a))
  (λ c →
    trans
      (cong (toB bc) (rightInverse ab (toA bc c)))
      (rightInverse bc c))

composedRoundTripStable :
  {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
  (ab : CertifiedRoundTrip A B) →
  (bc : CertifiedRoundTrip B C) → (a : A) →
  toA (composeRoundTrip ab bc) (toB (composeRoundTrip ab bc) a) ≡ a
composedRoundTripStable ab bc = leftInverse (composeRoundTrip ab bc)
