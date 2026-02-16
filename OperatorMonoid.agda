module OperatorMonoid where

open import Agda.Builtin.Equality
open import KernelAlgebra

------------------------------------------------------------------------
-- Endomorphism

Endo : ∀ {X} → Set
Endo {X} = State X → State X

------------------------------------------------------------------------
-- Composition

_∘_ : ∀ {X} → Endo {X} → Endo {X} → Endo {X}
(f ∘ g) s = f (g s)

------------------------------------------------------------------------
-- Closure under composition

record Generated {X : Set}
                 (K : Endo {X})
                 : Set where

  field
    closed :
      ∀ (f g : Endo {X}) → Endo {X}
