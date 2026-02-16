module KernelAlgebra where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

------------------------------------------------------------------------
-- Base ternary carrier

data T : Set where
  neg  : T
  zero : T
  pos  : T

------------------------------------------------------------------------
-- State space as indexed function

State : Set → Set
State X = X → T

------------------------------------------------------------------------
-- Involution

ι : ∀ {X} → State X → State X
ι s x with s x
... | neg  = pos
... | pos  = neg
... | zero = zero

ι²-id : ∀ {X} (s : State X) (x : X) → ι (ι s) x ≡ s x
ι²-id s x with s x
... | neg  = refl
... | pos  = refl
... | zero = refl


------------------------------------------------------------------------
-- Kernel operator interface

record Kernel {X : Set} : Set₁ where
  field
    K : State X → State X

    involutive-respecting :
      ∀ s → K (ι s) ≡ ι (K s)

open Kernel public
