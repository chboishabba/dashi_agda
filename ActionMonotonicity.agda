module ActionMonotonicity where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import KernelAlgebra
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)


------------------------------------------------------------------------
-- Action functional

record Action {X : Set} : Set₁ where
  field
    A : State X → Nat

open Action public

------------------------------------------------------------------------
-- Monotonicity property

record Monotone {X : Set}
                (K : State X → State X)
                (A : State X → Nat)
                : Set where

  field
    monotone :
      ∀ s → A (K s) ≤ A s
