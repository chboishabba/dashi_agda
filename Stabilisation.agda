module Stabilisation where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import KernelAlgebra

------------------------------------------------------------------------
-- Iteration

iterate : ∀ {X} →
          (State X → State X) →
          Nat →
          State X →
          State X
iterate K zero    s = s
iterate K (suc n) s = iterate K n (K s)

------------------------------------------------------------------------
-- No nontrivial 2-cycle

No2Cycle : ∀ {X} (K : State X → State X) → Set
No2Cycle K =
  ∀ s → iterate K 2 s ≡ s → K s ≡ s
