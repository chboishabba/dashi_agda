module DASHI.Combinatorics.Nontriviality where

open import DASHI.Core.Prelude

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

record IsNonTrivial (S : Set) : Set₁ where
  field
    x y : S
    x≢y : x ≢ y
