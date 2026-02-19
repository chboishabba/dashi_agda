module DASHI.Algebra.Quantum.UVFiniteness where

open import DASHI.Core.Prelude

record UVFinite (S : Set) : Set where
  field
    dim : S -> Nat
    bound : ∀ s -> dim s < 1000 -- example bound
