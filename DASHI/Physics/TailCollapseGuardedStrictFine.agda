module DASHI.Physics.TailCollapseGuardedStrictFine where

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (Nat; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.FiberContraction as FC

-- Guarded strictness interface for conditional projections using a Nat-valued metric.
record GuardedStrictnessFine {ℓ} : Set (lsuc ℓ) where
  field
    X : Set ℓ
    P : X → X
    d : X → X → Nat

    Guard  : X → Set
    Broken : X → Set
    Snap   : X → Set
    Restore : X → X

    -- Flow regime: strict contraction in the Nat-valued ultrametric.
    P-strict-on :
      ∀ {x y} →
      Guard x → Guard y →
      FC.FiberDistinct P x y →
      d (P x) (P y) < d x y

    -- Broken regime: restoration back into Guard.
    restore-normal-form :
      ∀ x → Broken x → Guard (Restore x)

    restore-idem :
      ∀ x → Restore (Restore x) ≡ Restore x

    restore-fixes :
      ∀ x → P (Restore x) ≡ Restore x

open GuardedStrictnessFine public
