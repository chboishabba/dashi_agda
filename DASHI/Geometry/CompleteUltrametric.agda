module DASHI.Geometry.CompleteUltrametric where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_; _<_; _≥_)
open import Ultrametric as UMetric

-- Cauchy sequence in an ℕ-valued ultrametric.
record Cauchy {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  open UMetric.Ultrametric U public
  field
    seq : Nat → S
    cauchy :
      ∀ ε → 0 < ε → Σ Nat (λ N →
        ∀ m n → N ≤ m → N ≤ n → d (seq m) (seq n) < ε)

record Complete {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  open UMetric.Ultrametric U public
  field
    limit : Cauchy U → S
    converges :
      (c : Cauchy U) →
      ∀ ε → 0 < ε → Σ Nat (λ N →
        ∀ n → N ≤ n → d (Cauchy.seq c n) (limit c) < ε)

open Cauchy public
open Complete public
