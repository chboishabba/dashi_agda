module DASHI.Geometry.LCP.Cauchy where

open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _,_)

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)

_≥_ : ℕ → ℕ → Set
m ≥ n = n ≤ m

-- Cauchy with modulus (constructive).
record CauchyMod {ℓ} {A : Set ℓ} (xs : ℕ → Stream A) : Set ℓ where
  field
    N : ℕ → ℕ
    mono : ∀ k j → k ≤ j → N k ≤ N j
    mod : ∀ k {m n} → N k ≤ m → N k ≤ n → lcp≥ (xs m) (xs n) k

open CauchyMod public
