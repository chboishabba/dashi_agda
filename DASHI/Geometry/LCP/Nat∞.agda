module DASHI.Geometry.LCP.Nat∞ where

open import Data.Nat using (ℕ; _≤_)
open import Data.Unit using (⊤)

-- Minimal ℕ∞ with just what we need for depth predicates.
data ℕ∞ : Set where
  fin : ℕ → ℕ∞
  ∞   : ℕ∞

_≥ᵏ_ : ℕ∞ → ℕ → Set
fin n ≥ᵏ k = k ≤ n
∞     ≥ᵏ k = ⊤

data _≤∞_ : ℕ∞ → ℕ∞ → Set where
  fin≤fin : ∀ {m n} → m ≤ n → fin m ≤∞ fin n
  fin≤∞   : ∀ {m}   → fin m ≤∞ ∞
  ∞≤∞     :               ∞ ≤∞ ∞
