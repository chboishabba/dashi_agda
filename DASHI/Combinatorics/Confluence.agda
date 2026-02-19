module DASHI.Combinatorics.Confluence where

open import DASHI.Core.Prelude

-- A nondeterministic one-step relation.
Rel : Set → Set₁
Rel S = S → S → Set

-- Diamond property: if s steps to s1 and s2, they can be joined.
Diamond : ∀ {S} → Rel S → Set
Diamond {S} step =
  ∀ s s₁ s₂ →
    step s s₁ →
    step s s₂ →
    Σ S (λ t → step s₁ t × step s₂ t)

-- Church-Rosser / confluence (standard).
postulate
  Confluent : ∀ {S} → Rel S → Set
