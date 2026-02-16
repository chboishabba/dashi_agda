module DASHI.Restoration where

open import DASHI.Prelude

record Restoration (S : Set) : Set₁ where
  field restore : S → S

Idempotent : ∀ {S} → (S → S) → Set
Idempotent f = ∀ x → f (f x) ≡ f x

record RestorationLaw {S : Set} (R : Restoration S) : Set where
  field
    idem : Idempotent (Restoration.restore R)
