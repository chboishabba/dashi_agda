module DASHI.Physics.TailCollapseGuardedStrict where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Ultrametric as UMetric
open import DASHI.Geometry.FiberContraction as FC

-- Guarded strictness interface for conditional projections.
-- This is the “Template B” shape: strictness only in flow regime.
record GuardedStrictness : Set₁ where
  field
    X : Set
    U : UMetric.Ultrametric X
    P : X → X

    Guard  : X → Set
    Broken : X → Set
    Snap   : X → Set
    Restore : X → X

    -- Flow regime: strictness on fibers (guarded).
    P-strict-on :
      ∀ {x y} →
      Guard x → Guard y →
      FC.FiberDistinct P x y →
      UMetric.Ultrametric.d U (P x) (P y) < UMetric.Ultrametric.d U x y

    -- Broken regime: restoration back into Guard.
    restore-normal-form :
      ∀ x → Broken x → Guard (Restore x)

    restore-idem :
      ∀ x → Restore (Restore x) ≡ Restore x

    restore-fixes :
      ∀ x → P (Restore x) ≡ Restore x

open GuardedStrictness public
