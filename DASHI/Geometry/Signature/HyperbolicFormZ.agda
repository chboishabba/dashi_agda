module DASHI.Geometry.Signature.HyperbolicFormZ where

open import Data.Integer using (ℤ; _*_; _+_; _-_; _≤_; _<_; +_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record CausalCountsZ (k : ℕ) : Set where
  field
    tau   : ℤ
    sigma : Vec ℤ k

open CausalCountsZ public

-- Sum of squares for a vector of ℤ.
sumSq : ∀ {k} → Vec ℤ k → ℤ
sumSq [] = + 0
sumSq (x ∷ xs) = (x * x) + sumSq xs

-- Hyperbolic quadratic form: a * tau^2 - b * |sigma|^2
F : ∀ {k} → ℤ → ℤ → CausalCountsZ k → ℤ
F {k} a b c =
  (a * ((tau c) * (tau c))) - (b * sumSq (sigma c))

-- Finite-speed cone: |sigma|^2 ≤ c^2 * tau^2
ConeBound : ∀ {k} → ℤ → CausalCountsZ k → Set
ConeBound {k} c q =
  sumSq (sigma q) ≤ (c * c) * ((tau q) * (tau q))

-- Exact cone boundary (lightlike).
ConeBoundary : ∀ {k} → ℤ → CausalCountsZ k → Set
ConeBoundary {k} c q =
  sumSq (sigma q) ≡ (c * c) * ((tau q) * (tau q))
