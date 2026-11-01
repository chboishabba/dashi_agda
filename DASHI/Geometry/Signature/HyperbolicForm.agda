module DASHI.Geometry.Signature.HyperbolicForm where

open import Data.Nat using (ℕ; _*_; _+_; _∸_; _^_; _≤_; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record CausalCounts (k : ℕ) : Set where
  field
    tau   : ℕ
    sigma : Vec ℕ k

open CausalCounts public

-- Sum of squares for a vector of Nat.
sumSq : ∀ {k} → Vec ℕ k → ℕ
sumSq [] = zero
sumSq (x ∷ xs) = (x * x) + sumSq xs

-- Hyperbolic quadratic form: a * tau^2 - b * |sigma|^2
F : ∀ {k} → ℕ → ℕ → CausalCounts k → ℕ
F {k} a b c =
  (a * ((tau c) ^ 2)) ∸ (b * sumSq (sigma c))

-- Finite-speed cone: |sigma|^2 ≤ c^2 * tau^2
ConeBound : ∀ {k} → ℕ → CausalCounts k → Set
ConeBound {k} c q =
  sumSq (sigma q) ≤ (c * c) * ((tau q) ^ 2)

-- Exact cone boundary (lightlike).
ConeBoundary : ∀ {k} → ℕ → CausalCounts k → Set
ConeBoundary {k} c q =
  sumSq (sigma q) ≡ (c * c) * ((tau q) ^ 2)
