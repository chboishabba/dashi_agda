module DASHI.Geometry.LCP.Stream where

open import Data.Nat using (ℕ; _<_) 
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Functional streams.
Stream : ∀ {ℓ} → Set ℓ → Set ℓ
Stream A = ℕ → A

-- LCP predicate: agree on first k digits.
Depth≥ : ∀ {ℓ} {A : Set ℓ} → Stream A → Stream A → ℕ → Set ℓ
Depth≥ xs ys k = ∀ i → i < k → xs i ≡ ys i

lcp≥ : ∀ {ℓ} {A : Set ℓ} → Stream A → Stream A → ℕ → Set ℓ
lcp≥ = Depth≥
