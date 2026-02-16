module FascisticSystem where

open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Nat as Nat
open import Data.Bool using (Bool; true; false)



-- Abstract finite state space

postulate
  S : Set
  finiteS : ℕ          -- cardinality (not constructively used)

-- Entropy function (measure into ℕ for simplicity)

postulate
  H : S → ℕ

-- Projection operator (idempotent, non-invertible)

record Projection : Set where
  field
    K        : S → S
    idemp    : ∀ s → K (K s) ≡ K s
    contract : ∀ s → H (K s) ≤ H s

-- System = list of projections applied in fixed order

postulate
  Ktotal : S → S

-- Global contraction property

postulate
  monotone : ∀ s → H (Ktotal s) ≤ H s

-- Strict decrease when not in fixed set

postulate
  strict-decrease :
    ∀ s → H (Ktotal s) < H s ⊎ (Ktotal s ≡ s)

-- Define attractor

Attractor : Set
Attractor = Σ S (λ s → Ktotal s ≡ s)

-- Iteration

iterate : ℕ → S → S
iterate zero    s = s
iterate (suc n) s = Ktotal (iterate n s)
