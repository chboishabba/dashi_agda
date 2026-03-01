module DASHI.Physics.TailCollapseGuardedStrict where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)

-- Guarded strictness interface for conditional projections.
-- This is the “Template B” shape: strictness only in flow regime.
record GuardedStrictness {ℓ} {A : Set ℓ} : Set (lsuc ℓ) where
  field
    X : Set ℓ
    P : X → X

    proj : X → Stream A

    Guard  : X → Set
    Broken : X → Set
    Snap   : X → Set
    Restore : X → X

    κ : ℕ

    -- Flow regime: strictness in LCP depth (or your chosen Ball predicate).
    P-strict-on :
      ∀ {x y k} →
      Guard x → Guard y →
      lcp≥ (proj x) (proj y) k →
      lcp≥ (proj (P x)) (proj (P y)) (k + κ)

    -- Broken regime: restoration back into Guard.
    restore-normal-form :
      ∀ x → Broken x → Guard (Restore x)

    restore-idem :
      ∀ x → Restore (Restore x) ≡ Restore x

    restore-fixes :
      ∀ x → P (Restore x) ≡ Restore x

open GuardedStrictness public
