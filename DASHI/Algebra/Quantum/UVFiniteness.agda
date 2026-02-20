module DASHI.Algebra.Quantum.UVFiniteness where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_)

-- Abstract bounded-dimension bundle.
record UVBounded : Set₁ where
  field
    L : Set
    dimH : L → Nat
    bound : L → Nat
    dimH≤bound : ∀ l → dimH l ≤ bound l

record UVFinite (B : UVBounded) : Set where
  field
    finiteModes : ∀ l → Σ Nat (λ N → UVBounded.dimH B l ≤ N)

uvFiniteness :
  ∀ B → UVFinite B
uvFiniteness B =
  record
    { finiteModes = λ l → UVBounded.bound B l , UVBounded.dimH≤bound B l
    }
