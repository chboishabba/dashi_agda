{-# OPTIONS --safe #-}
module DASHI.Physics.UniversalityTheorem where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)

-- Canonical quotient-style universality for a map C : S → S.
record Universality {S : Set} (C : S → S) : Set₁ where
  field
    Q    : Set
    π    : S → Q
    lift : ∀ {Y : Set} → (f : S → Y) → (∀ x → f (C x) ≡ f x) → Q → Y
    fac  : ∀ {Y : Set} (f : S → Y) (resp : ∀ x → f (C x) ≡ f x) →
             ∀ x → lift f resp (π x) ≡ f x

open Universality public

-- Default (non-unique) universality: Q = S, π = C, lift = f.
canonicalUniversality : ∀ {S : Set} (C : S → S) → Universality C
canonicalUniversality {S} C =
  record
    { Q = S
    ; π = C
    ; lift = λ f _ → f
    ; fac = λ f resp x → resp x
    }
