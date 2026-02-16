module DASHI.NonTriviality where

open import DASHI.Prelude

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

record NonTrivial (S : Set) : Set₁ where
  field
    x y : S
    x≢y : x ≢ y
